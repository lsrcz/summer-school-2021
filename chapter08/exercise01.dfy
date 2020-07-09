// You will build a sharded hash table.
//
// "Hash table" is the application
// specification; we provide the application-visible messages that must survive
// message projection. Your distributed protocol will introduce new messages.
//
// "Sharded" means that you will divide responsibility for managing keys across
// participating nodes. You do not need to implement replication; if a node fails,
// it may leave a set of keys inaccessible.

datatype AppMessage =
    InsertRequest(key: int, value: int)
  | InsertReply(key: int, value: int)
  | QueryRequest(key: int)
  | QueryReply(key: int, value: int)
