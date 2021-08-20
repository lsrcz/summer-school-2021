//#title Protocol file
//#desc Define your protocol implementation here: message type, state machine

include "network.s.dfy"

// Define your Message datatype here.
datatype Message = Message(/* FILL ME IN! */)

// Define your Host protocol state machine here.
datatype HostVars = HostVars(/* FILL ME IN! */)

predicate HostInit(v:HostVars, id:HostId) {
  true // Replace me
}

// The (trusted) DistributedSystem helpfully tells the host what its id is,
// so the host can tell which messages are addressed to it. In a real system,
// that id would be a constant part of the hosts' state; here we're trying
// to keep the boilerplate to a minimum.
predicate HostNext(id:HostId, v:HostVars, v':HostVars, a:NetAction<Message>) {
  true // Replace me
}
