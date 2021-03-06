import stainless.lang._
import stainless.collection._
import stainless.proof._
import stainless.annotation._

import scala.language.postfixOps

import actors._

object LeaderElection {
  // following https://en.wikipedia.org/wiki/Chang_and_Roberts_algorithm

  case class Initialize(next: ActorRef, uid: BigInt) extends Msg
  case object StartElection extends Msg
  case class Election(@ghost startingActor: ActorRef, i: BigInt) extends Msg
  // startingActor is used only in proofs
  case class Elected(i: BigInt) extends Msg

  def max(x: BigInt, y: BigInt) = if (x > y) x else y

  case class Uninitialized() extends Behavior {
    override def processMsg(msg: Msg)(implicit ctx: ActorContext) = {
      msg match {
        case Initialize(next, uid) => NonParticipant(next, uid)

        case _ => this
      }
    }
  }

  case class NonParticipant(next: ActorRef, uid: BigInt) extends Behavior {
    override def processMsg(msg: Msg)(implicit ctx: ActorContext) = {
      msg match {
        case StartElection =>
          next ! Election(ctx.self, uid)
          Participant(next, uid)

        case Election(startingActor, uid2) =>
          next ! Election(startingActor, max(uid, uid2))
          Participant(next, uid)

        case _ => this
      }
    }
  }

  case class Participant(next: ActorRef, uid: BigInt) extends Behavior {
    override def processMsg(msg: Msg)(implicit ctx: ActorContext) = {
      msg match {
        case Elected(leader) =>
          next ! Elected(leader)
          KnowLeader(next, leader, uid)

        case Election(startingActor, uid2) =>
          if (uid == uid2) {
            // I'm the leader!!
            next ! Elected(uid)
            KnowLeader(next, uid, uid)
          } else if (uid2 > uid) {
            next ! Election(startingActor, uid2)
            this
          } else {
            // discard smaller uid Election message
            this
          }

        case _ => this
      }
    }
  }

  case class KnowLeader(next: ActorRef, leader: BigInt, uid: BigInt) extends Behavior

  @ignore
  def main(args: Array[String]): Unit = {
    if (args.length != 1) {
      println("Usage: run NUMBER_OF_PARTICIPANTS")
      System.exit(1)
    }
    val participants = args(0).toInt
    val system = akka.actor.ActorSystem("LeaderElection")

    val uids = (1 to participants).map(i => i -> BigInt(scala.util.Random.nextInt(1000))).toMap
    println("UID of the participants:")
    println(uids.toList.sortBy(_._1).mkString("\n"))

    val actorRefs = (1 to participants).map(i =>
      i ->
        ActorRef(
          "Process(" + i.toString + "," + uids(i) + ")",
          system.actorOf(
            akka.actor.Props(new ActorWrapper(new Uninitialized())),
            name = i.toString,
          )
        )
    ).toMap

    // We first initialize each actor by setting up their `next` actor
    for (i <- 1 to participants) {
      implicit val ctx = ActorContext(actorRefs(i), Nil())
      actorRefs(i) ! Initialize(actorRefs(i % participants + 1), uids(i))
    }

    // Then we wait a bit
    Thread.sleep(1000)

    // And we start an election by sending a message to the first actor
    implicit val ctx = ActorContext(actorRefs(1), Nil())
    actorRefs(1) ! StartElection
  }
}
