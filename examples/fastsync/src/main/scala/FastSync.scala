import stainless.lang._
import stainless.proof.check
import stainless.collection._
import stainless.annotation._
import stainless.math.max
import stainless.math.min

import scala.util.Random

import actors._

/*******************************************************************************
 * Code adapted from:
 * https://github.com/interchainio/verification/blob/05d1d632267be88d55e4e91e9dc328aa6e2dff3f/spec/fastsync.tla
 *
 * A few differences:
 * - No invariant is proven yet
 * - Not all cases were implemented yet
 * - Some TLA `CHOOSE` have been replaced by deterministic `find` (iterating over a list)
 * - Here we didn't use maps to `None` but instead a map with a `List` as a domain, is that correct?
 * - Output events are not modelled here
 * - Not clear if we can model liveness guarantees
 * - A `main` function should be written (to try out the actors)
 *******************************************************************************/

object FastSync {

  @extern @opaque
  def assume(b: Boolean): Unit = {
    ??? : Unit
  } ensuring(_ => b)

  sealed abstract class State
  case object Init extends State
  case object WaitForPeer extends State
  case object WaitForBlock extends State
  case object Finished extends State

  case object StartFSM extends Msg
  case object StopFSM extends Msg
  case class StatusResponse(peerId: ActorRef, height: BigInt) extends Msg
  case class BlockResponse(peerId: ActorRef, height: BigInt, block: Block) extends Msg
  case class StateTimeout(state: State) extends Msg
  case class PeerRemove(peerIds: List[ActorRef]) extends Msg
  case class ProcessedBlock(err: Boolean) extends Msg
  case class MakeRequests(maxNumRequests: BigInt) extends Msg

  case class Block(id: BigInt, valid: Boolean)

  case class Pool(
    height: BigInt,
    peers: List[ActorRef],
    peerHeights: IterableMap[ActorRef, BigInt],
    maxPeerHeight: BigInt,
    blocks: IterableMap[BigInt, ActorRef],
    nextRequestHeight: BigInt,
    ghostReceivedBlocks: List[BigInt],
    ghostProcessedHeights: List[BigInt]
  ) {
    require(definedHeights(peers, peerHeights))
  }

  @opaque
  def diffForall[T](@induct l1: List[T], l2: List[T], p: T => Boolean): Unit = {
    require(l1.forall(p))
    ()
  } ensuring(_ => (l1 -- l2).forall(p))

  def definedHeights(pool: Pool): Boolean = definedHeights(pool.peers, pool.peerHeights)

  def definedHeights(peers: List[ActorRef], peerHeights: IterableMap[ActorRef, BigInt]) =
    peers.forall(r => peerHeights.contains(r))

  def findMaxPeerHeight(activePeers: List[ActorRef], heights: IterableMap[ActorRef, BigInt]): BigInt = {
    require(definedHeights(activePeers, heights))

    activePeers match {
      case Nil() => 0
      case Cons(r, rs) => max(heights(r), findMaxPeerHeight(rs, heights))
    }
  }

  def removePeers(pool: Pool, ids: List[ActorRef]): Pool = {
    require(definedHeights(pool))

    val Pool(height, peers, peerHeights, maxPeerHeight, blocks, nextRequestHeight, _, _) = pool
    val newPeers = peers -- ids
    val newBlocks = pool.blocks.filter(h => pool.blocks.contains(h) && ids.contains(pool.blocks(h)))
    diffForall(peers, ids, (r: ActorRef) => pool.peerHeights.contains(r))
    val newMph = findMaxPeerHeight(newPeers, peerHeights)
    val newNrh = min(newMph + 1, nextRequestHeight)
    pool.copy(peers = newPeers, maxPeerHeight = newMph, blocks = newBlocks, nextRequestHeight = newNrh)
  }

  def removeShortPeers(pool: Pool, h: BigInt): Pool = {
    require(definedHeights(pool))
    removePeers(pool, pool.peers.filter(r =>
      pool.peerHeights.contains(r) &&
      pool.peerHeights(r) < h
    ))
  }

  def removeBadPeers(pool: Pool): Pool = {
    require(definedHeights(pool))
    removeShortPeers(pool, pool.height)
  }

  def isPeerAtHeight(pool: Pool, r: ActorRef, h: BigInt): Boolean = {
    pool.peers.contains(r) &&
    pool.blocks.contains(h) &&
    pool.blocks(h) == r &&
    pool.ghostReceivedBlocks.contains(h)
  }

  def atHeightOrNone(pool: Pool, r: Option[ActorRef], h: BigInt): Boolean = {
    (!r.isEmpty && isPeerAtHeight(pool, r.get, h)) ||
    (r.isEmpty && pool.peers.forall(q => !isPeerAtHeight(pool, q, h)))
  }

  def optionToList[T](o: Option[T]): List[T] = o match {
    case None() => List()
    case Some(x) => List(x)
  }

  def invalidateFirstTwoBlocks(pool: Pool, p1: Option[ActorRef], p2: Option[ActorRef]): Pool = {
    require(definedHeights(pool))
    if (atHeightOrNone(pool, p1, pool.height) || atHeightOrNone(pool, p2, pool.height + 1))
      removePeers(pool, optionToList(p1) ++ optionToList(p2))
    else
      pool
  }

  @opaque
  def definedHeightsUpdated(@induct peers: List[ActorRef], heights: IterableMap[ActorRef, BigInt], r: ActorRef, h: BigInt): Unit = {
    require(definedHeights(peers, heights))
    ()
  } ensuring(_ => definedHeights(peers, heights.updated(r, h)))

  def updatePeer(pool: Pool, peerId: ActorRef, height: BigInt): Pool = {
    require(definedHeights(pool))

    if (pool.peers.contains(peerId)) {
      if (height < pool.height) {
        pool
      } else {
        val newPeers = Cons(peerId, pool.peers)
        val newPh = pool.peerHeights.updated(peerId, height)
        definedHeightsUpdated(pool.peers, pool.peerHeights, peerId, height) // ensures definedHeights(pool.peers, newPh)
        val newMph = findMaxPeerHeight(newPeers, newPh)
        pool.copy(peers = newPeers, peerHeights = newPh, maxPeerHeight = newMph)
      }
    } else {
      if (pool.peerHeights.contains(peerId) && height < pool.peerHeights(peerId)) {
        removePeers(pool, List(peerId))
      } else {
        val newPh = pool.peerHeights.updated(peerId, height)
        definedHeightsUpdated(pool.peers, pool.peerHeights, peerId, height) // ensures definedHeights(pool.peers, newPh)
        val newMph = findMaxPeerHeight(pool.peers, newPh)
        pool.copy(peerHeights = newPh, maxPeerHeight = newMph)
      }
    }

  } ensuring(res => definedHeights(res))

  def range(i: BigInt, j: BigInt): List[BigInt] = {
    if (i > j) List()
    else Cons(i, range(i+1, j))
  }

  case class FSM(state: State, pool: Pool) extends Behavior {

    override def processMsg(m: Msg)(implicit ctx: ActorContext) = {
      (state, m) match {
        case (Init, StartFSM) => FSM(WaitForPeer, pool)

        case (WaitForPeer, StatusResponse(peerId, height)) =>
          val newPool = updatePeer(pool, peerId, height)
          val newState = if (newPool.peers.isEmpty) state else WaitForBlock
          FSM(newState, newPool)
        case (WaitForPeer, StateTimeout(WaitForPeer)) => FSM(Finished, pool)
        case (WaitForPeer, StopFSM) => FSM(Finished, pool)

        case (WaitForBlock, MakeRequests(maxNumRequests)) =>
          val cleanPool = removeBadPeers(pool)
          val pendingBlocks = cleanPool.blocks.domain
          val numPendingBlocks = pendingBlocks.length
          val newNrh = min(
            cleanPool.maxPeerHeight,
            cleanPool.nextRequestHeight + maxNumRequests - numPendingBlocks
          )
          val heights = range(cleanPool.nextRequestHeight, newNrh - 1)

          // In `newBlocks`, we use a deterministic `choose` (with `find`) instead of a non-deterministic one as in TLA
          val newBlocks = heights.foldLeft(cleanPool.blocks) { case (acc, h) =>
            cleanPool.peers.find { p =>
              cleanPool.peerHeights.contains(p) && cleanPool.peerHeights(p) == h
            } match {
              case None() => acc
              case Some(p) => acc.updated(h, p)
            }
          }
          val newPool = cleanPool.copy(blocks = newBlocks, nextRequestHeight = newNrh)
          FSM(WaitForBlock, newPool)

        case (WaitForBlock, StatusResponse(peerId, height)) =>
          val newPool = updatePeer(pool, peerId, height)
          if (newPool.height >= newPool.maxPeerHeight) FSM(Finished, newPool)
          else if (newPool.peers.isEmpty) FSM(WaitForPeer, newPool)
          else FSM(WaitForBlock, newPool)

        case (WaitForBlock, BlockResponse(peerId, height, block)) =>
          val newPool = if (
            !block.valid ||
            !pool.blocks.contains(height) ||
            peerId != pool.blocks(height) ||
            !pool.peers.contains(peerId)
          ) {
            removePeers(pool, List(peerId))
          }
          else {
            pool.copy(ghostReceivedBlocks = Cons(height, pool.ghostReceivedBlocks))
          }
          val newState = if (newPool.peers.isEmpty) WaitForPeer else WaitForBlock
          FSM(newState, newPool)

        case (WaitForBlock, ProcessedBlock(err)) =>
          val newPool = if (
            !pool.blocks.contains(pool.height) ||
            !pool.blocks.contains(pool.height + 1)
          ) {
            pool
          } else if (err) {
            // FIXME: how to pick p1, p2?
            (??? : Pool)
          } else {
            val newBlocks = pool.blocks.remove(pool.height)
            val newHeight = pool.height + 1
            val newGph = Cons(pool.height, pool.ghostProcessedHeights)
            val newPool = pool.copy(blocks = newBlocks, height = newHeight, ghostProcessedHeights = newGph)
            removeShortPeers(newPool, newHeight)
          }
          val newState = if (newPool.height >= pool.maxPeerHeight) Finished else WaitForBlock
          FSM(newState, newPool)

        case (WaitForBlock, PeerRemove(peerIds)) =>
          val newPool = removePeers(pool, peerIds)
          val newState =
            if (newPool.peers.isEmpty) WaitForPeer
            else if (newPool.height >= newPool.maxPeerHeight) Finished
            else WaitForBlock

          FSM(newState, newPool)

        case (WaitForBlock, StateTimeout(WaitForBlock)) =>
          // TODO: fix newPool by using deterministic code
          val newPool = (??? : Pool)
          val newState =
            if (newPool.peers.isEmpty) WaitForPeer
            else if (newPool.height >= newPool.maxPeerHeight) Finished
            else WaitForBlock

          FSM(newState, newPool)

        case (WaitForBlock, StopFSM) => FSM(Finished, pool)

        case (_, _) => this
      }
    }

  }

  @ignore
  def main(args: Array[String]): Unit = {
    if (args.length != 1) {
      println("Usage: run NUMBER_OF_PARTICIPANTS")
      System.exit(1)
    }
    val participants = args(0).toInt
    val system = akka.actor.ActorSystem("Interchain")

    println("HELLO WORLD")

    // val uids = (1 to participants).map(i => i -> BigInt(scala.util.Random.nextInt(1000))).toMap
    // println("UID of the participants:")
    // println(uids.toList.sortBy(_._1).mkString("\n"))

    // val actorRefs = (1 to participants).map(i =>
    //   i ->
    //     ActorRef(
    //       "Process(" + i.toString + "," + uids(i) + ")",
    //       system.actorOf(
    //         akka.actor.Props(new ActorWrapper(new Uninitialized())),
    //         name = i.toString,
    //       )
    //     )
    // ).toMap

    // // We first initialize each actor by setting up their `next` actor
    // for (i <- 1 to participants) {
    //   implicit val ctx = ActorContext(actorRefs(i), Nil())
    //   actorRefs(i) ! Initialize(actorRefs(i % participants + 1), uids(i))
    // }

    // // Then we wait a bit
    // Thread.sleep(1000)

    // // And we start an election by sending a message to the first actor
    // implicit val ctx = ActorContext(actorRefs(1), Nil())
    // actorRefs(1) ! StartElection
  }
}
