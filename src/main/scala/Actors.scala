import stainless.lang._
import stainless.collection._
import stainless.annotation._

import scala.annotation.meta.field

object actors {

  @library
  abstract class Msg

  @library
  abstract class Behavior {
    def processMsg(msg: Msg)(implicit ctx: ActorContext): Behavior = this
  }

  @library
  case class ActorRef(
    name: String,
    @(extern @field) @(pure @field)
    underlying: akka.actor.ActorRef
  ) {

    @inline
    def !(msg: Msg)(implicit ctx: ActorContext): Unit = {
      ctx.send(this, msg)
    }
  }

  @library
  case class ActorContext(
    self: ActorRef,
    @ghost
    var toSend: List[(ActorRef, Msg)] = Nil()
  ) {

    @inline
    def send(to: ActorRef, msg: Msg): Unit = {
      ghost {
        toSend = (to, msg) :: toSend
      }

      sendUnderlying(to, msg)
    }

    @extern @pure
    private def sendUnderlying(to: ActorRef, msg: Msg): Unit = {
      to.underlying ! msg
    }
  }

  @ghost @library
  case class ActorSystem(
    behaviors: CMap[ActorRef, Behavior],
    inboxes: CMap[(ActorRef, ActorRef), List[Msg]]
  ) {

    def step(from: ActorRef, to: ActorRef): ActorSystem = {
      inboxes(from -> to) match {
        case Nil() =>
          this

        case Cons(msg, msgs) =>
          val (newBehavior, toSend) = deliverMessage(to, msg)

          val newBehaviors = behaviors.updated(to, newBehavior)
          val newInboxes = toSend.reverse.foldLeft(inboxes.updated(from -> to, msgs)) {
            case (acc, (dest, m)) => acc.updated(to -> dest, acc(to -> dest) :+ m)
          }

          ActorSystem(newBehaviors, newInboxes)
      }
    }

    def deliverMessage(actor: ActorRef, msg: Msg): (Behavior, List[(ActorRef, Msg)]) = {
      val behavior = behaviors(actor)

      val ctx = ActorContext(actor, Nil())
      val nextBehavior = behavior.processMsg(msg)(ctx)

      (nextBehavior, ctx.toSend)
    }
  }

  @ignore
  class ActorWrapper(initialBehavior: Behavior) extends akka.actor.Actor with akka.actor.ActorLogging {

    private def handler(behavior: Behavior): PartialFunction[Any, Unit] = {
      case msg: Msg =>
        val me = ActorRef(context.self.path.name, context.self)
        val ctx = ActorContext(me, Nil())
        val newBehavior = behavior.processMsg(msg)(ctx)

        log.info(s"Received: $msg, becoming $newBehavior")
        context.become(handler(newBehavior), discardOld = true)
    }

    def receive = handler(initialBehavior)
  }

}
