Your goal is to model a lock service that consists of a single server and an arbitrary number of clients. The server provides the functionality of an exclusive lock. Initially, the server holds the lock. A client can acquire the lock (if the lock is currently held by the server) or it can return the lock (if it currently holds it). 

Do not model the network. 

Your state machine should reflect the state of the entire distributed system; so it’s OK to have a single transition that atomically modifies the state of multiple nodes in the system. 

