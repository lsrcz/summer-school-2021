//#instructor The switch is an example of a very simple state machine.
//#instructor All its steps are non-parameterized.
//#instructor This example is intended to show the basic of the boilerplate
//#instructor of a TLA+ state machine embedded in Dafny.

datatype SwitchState = On | Off

datatype State = State(switch:SwitchState)

predicate Init(s:State) {
    s.switch == Off
}

predicate Activate(s:State, s':State) {
    s'.switch == On
}

predicate Deactivate(s:State, s':State) {
    s'.switch == Off
}

predicate Toggle(s:State, s':State) {
    s'.switch == if s.switch.On? then Off else On
}

predicate Next(s:State, s':State) {
    || Activate(s, s')
    || Deactivate(s, s')
    || Toggle(s, s')
}
