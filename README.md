1. Install Docker itself if you don't have it already.

  a. Mac installer

  a. Windows installer

  a. On linux:

sudo apt install docker.io
sudo service docker restart
sudo addgroup $USER docker
newgrp docker
Pull the image. (This is the slow thing; it includes a couple GB of Ubuntu.)
    docker pull jonhdotnet/veribetrfs:1.0
Test that the image works
​    docker container run -t -i jonhdotnet/veribetrfs:1.0 /bin/bash
    dafny test.dfy

If everything is working, you should see:
Dafny 2.3.0.10506
test.dfy(3,0): Error BP5003: A postcondition might not hold on this return path.

test.dfy(2,12): Related location: This is the postcondition that might not hold.

Execution trace:

    (0,0): anon0

 

Dafny program verifier finished with 0 verified, 1 error



4. Run the image connected to your filesystem so you can edit in your OS, and then run Dafny from inside the docker container:




mkdir work
cd work
docker container run -t -i --mount src="`pwd`",target=/home/dafnyserver/work,type=bind --workdir /home/dafnyserver/work jonhdotnet/veribetrfs:1.0 /bin/bash
cp -r ../tutorial .
cd tutorial/chapter01
