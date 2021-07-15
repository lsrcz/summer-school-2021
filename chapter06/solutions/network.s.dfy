//////////////////////////////////////////////////////////////////////////////
// Some handy global definitions
//////////////////////////////////////////////////////////////////////////////

// A global constant telling us how many hosts are participating.  It's a
//

// A global constant telling us how many hosts are participating.  It's a
// constant so we don't have to prove it doesn't change as the execution
// evolves.
function NumHosts() : nat
  ensures NumHosts() > 0

// "newtype" means that HostId is just an int ... except that it always
// satisfies 0 <= b < NumHosts().
// ("nat" is "newtype nat = b: int | 0 <= b".)
newtype HostId = b: int | 0 <= b < NumHosts()

// The set of all host identities.
function AllHosts() : set<HostId> {
  set h:HostId | true     // ignore the "No terms found" warning.
}


//////////////////////////////////////////////////////////////////////////////
// Network
//////////////////////////////////////////////////////////////////////////////

// DO NOT EDIT THIS FILE! It's a trusted file that specifies how the network
// delivers packets, allowing reorder and duplicate delivery.

// Option is a common type we usually keep in our standard library.
datatype Option<V> = None | Some(value:V)

// The binding between a host step and a network step:
// if the host thinks it received na.rcv, then the network must agree
// such a packet is ready to be received at the host.
// Likewise, if the network is going to accept na.send for later delivery,
// the host had better agree it wanted to send those packets.
datatype NetAction<M> = NetAction(rcv:Option<M>, send:set<M>)

// Once a host has sent a message, messagesEverSent
datatype NetState<M> = NetState(messagesEverSent:set<M>)

predicate NetInit(v:NetState) {
  v.messagesEverSent == {}
}

predicate NetNext(v:NetState, v':NetState, a:NetAction) {
  && (a.rcv.Some? ==> a.rcv.value in v.messagesEverSent)
  && v'.messagesEverSent == v.messagesEverSent + a.send
  // A fancier network might constrain hosts to only send messages with correct
  // source addresses. In this exercise, you define the message structure, so
  // we're not going to enforce anything here.
}
