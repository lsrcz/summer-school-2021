// TODO Manos suggests using modulo for positions instead of links
datatype NodeConstants = NodeConstants(neighbor: nat)
datatype Node = Node(highest_heard: nat)

datatype Constants = Constants(nodes: seq<Node>)
datatype Variables = Variables(nodes: seq<Node>)

predicate IsLeader(k: Constants, s: Variables, i: nat)
{
  s.nodes[i].highest_heard == i
}

predicate Safety(k: Constants, s: Variables)
{
  forall i, j | IsLeader(k, s, i) && IsLeader(k, s, j) :: i == j
}

predicate Receive(k: Constants, s: Variables, s': Variables, src: nat, dst: nat)
{
  && k.nodes
  && var neighbor_highest := 
  && s' == s.[dst := Node(neighbor_highest)]
}

predicate Next(k: Constants, s: Variables, s': Variables)
{
  && 
}
