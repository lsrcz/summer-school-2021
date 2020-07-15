// Your protocol: message type, state machine

include "network.s.dfy"

// Define your Message datatype here.
datatype Message = Grant(dest:HostId, epoch:nat)

// Define your Host protocol state machine here.
datatype HostState = HostState(holdsLock:bool, epoch:nat)

predicate HostInit(s:HostState, id:HostId) {
  && s.holdsLock == (id == 0)
  && s.epoch == if id == 0 then 1 else 0
}

predicate DoGrant(s:HostState, s':HostState, a:NetAction<Message>, recipient:HostId) {
  && s.holdsLock == true
  && a.rcv.None?
  && a.send == {Grant(recipient, s.epoch + 1)}
  && s'.holdsLock == false
  && s'.epoch == s.epoch
}

predicate DoAccept(id:HostId, s:HostState, s':HostState, a:NetAction<Message>) {
  && a.rcv.Some?
  && a.rcv.value.dest == id
  && a.rcv.value.epoch > s.epoch
  && a.send == {}
  && s'.epoch == a.rcv.value.epoch
  && s'.holdsLock == true
}

// The (trusted) DistributedSystem helpfully tells the host what its id is,
// so the host can tell which messages are addressed to it. In a real system,
// that id would be a constant part of the hosts' state; here we're trying
// to keep the boilerplate to a minimum.
predicate HostNext(id:HostId, s:HostState, s':HostState, a:NetAction<Message>) {
  || (exists recipient :: DoGrant(s, s', a, recipient) )
  || DoAccept(id, s, s', a)
}
