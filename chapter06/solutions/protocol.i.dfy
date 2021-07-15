// Your protocol: message type, state machine

include "network.s.dfy"

// Define your Message datatype here.
datatype Message = Grant(dest:HostId, epoch:nat)

// Define your Host protocol state machine here.
datatype HostVars = HostVars(holdsLock:bool, epoch:nat)

predicate HostInit(v:HostVars, id:HostId) {
  && v.holdsLock == (id == 0)
  && v.epoch == if id == 0 then 1 else 0
}

predicate DoGrant(v:HostVars, v':HostVars, a:NetAction<Message>, recipient:HostId) {
  && v.holdsLock == true
  && a.rcv.None?
  && a.send == {Grant(recipient, v.epoch + 1)}
  && v'.holdsLock == false
  && v'.epoch == v.epoch
}

predicate DoAccept(id:HostId, v:HostVars, v':HostVars, a:NetAction<Message>) {
  && a.rcv.Some?
  && a.rcv.value.dest == id
  && a.rcv.value.epoch > v.epoch
  && a.send == {}
  && v'.epoch == a.rcv.value.epoch
  && v'.holdsLock == true
}

// The (trusted) DistributedSystem helpfully tells the host what its id is,
// so the host can tell which messages are addressed to it. In a real system,
// that id would be a constant part of the hosts' state; here we're trying
// to keep the boilerplate to a minimum.
predicate HostNext(id:HostId, v:HostVars, v':HostVars, a:NetAction<Message>) {
  || (exists recipient :: DoGrant(v, v', a, recipient) )
  || DoAccept(id, v, v', a)
}
