 // case analysis step 1: dst changed. Was it between start,end,
        // equal to start or end, or on the opposide side (end,start)?
        // answer -> only dst==end matters.


          // case analysis step 2:
          // did dst take on k.ids[src], v.highest_heard[src], or
          // v.highest_heard[dst]?
              // src now included in extended chord.
              // Covered by prior-state chord.
            ...becmose a Between argument that reveals UniqueIDs problem.

            // dst got src's id, and that was *higher* than src's highest
            // heard,
            // which means that this chord must have started at src.
            

Okay, so my fellow verification engineer banged out this lovely specification for
leader election.
Let's read it.

Alex the Engineer had to go on vacation before completing the proof work, so Alex left me
with this file. Let's get it verifying!
We'll study the spec carefully.
Then we'll begin by assuming the protocol is correct and try to figure out why
stupid old Dafny doesn't understand Alex's brilliance.

docker container run -t -i --mount src="`pwd`",target=/home/dafnyserver/work,type=bind --workdir /home/dafnyserver/work jonhdotnet/summer_school:1.1 /bin/bash

- fix the type inference failures on nat
- in my test run, it got really slow. Add /timeLimit:20


***
Image fixes:
- dafny-profile.py
- pip3 install termcolor
