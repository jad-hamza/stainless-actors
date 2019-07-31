import stainless.lang._
import stainless.collection._

case class IterableMap[A,B](domain: List[A], m: CMap[A,B]) {
  // slow implementation due to non-constant-time lookups in domain
  // maybe add a Set[A]

  def contains(key: A) = domain.contains(key)

  def updated(key: A, value: B): IterableMap[A,B] = {
    val newM = m.updated(key, value)
    if (domain.contains(key)) IterableMap(domain, newM)
    else IterableMap(Cons(key, domain), newM)
  }

  def remove(key: A): IterableMap[A,B] = IterableMap(domain - key, m)

  def apply(key: A): B = {
    require(domain.contains(key))
    m(key)
  }

  def get(key: A): Option[B] = {
    if (domain.contains(key)) Some(m(key))
    else None()
  }

  def getOrElse(key: A, value: B): B = {
    if (domain.contains(key)) m(key)
    else value
  }

  def filter(p: A => Boolean) = IterableMap(domain.filter(p), m)
}
