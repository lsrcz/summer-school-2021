include "../chapter05/framework.s.dfy"

datatype AppMessage =
    InsertRequest(key: int, value: int)
  | InsertReply(key: int, value: int)
  | QueryRequest(key: int)
  | QueryReply(key: int, value: int)

datatype Message =
    Message
