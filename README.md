# Install Docker itself if you don't have it already.

  * [Mac installer](https://docs.docker.com/v17.12/docker-for-mac/install/)

  * [Windows installer](https://docs.docker.com/v17.12/docker-for-windows/install/)

  * On linux:

```bash
sudo apt install docker.io
sudo service docker restart
sudo addgroup $USER docker
newgrp docker
```

# Pull the image.
(This is the slow thing; it includes a couple GB of Ubuntu.)

```bash
    docker pull jonhdotnet/summer_school:1.1
```

# Test that the image works
```bash
    docker container run -t -i jonhdotnet/summer_school:1.1 /bin/bash
    dafny test.dfy
    exit
```

If everything is working, you should see:

```bash
/home/dafnyserver/test.dfy(6,0): Error: A postcondition might not hold on this return path.
/home/dafnyserver/test.dfy(5,12): Related location: This is the postcondition that might not hold.
Execution trace:
    (0,0): anon0

Dafny program verifier finished with 0 verified, 1 error
```

# Run the image

Run the image connected to your filesystem so you can edit in your OS, and then run Dafny from inside the docker container:

```bash
mkdir work
cd work
docker container run -t -i --mount src="`pwd`",target=/home/dafnyserver/work,type=bind --workdir /home/dafnyserver/work jonhdotnet/summer_school:1.1 /bin/bash
git clone https://github.com/GLaDOS-Michigan/summer-school-2021.git
cd summer-school-2021/chapter01-basics
```

Now you can edit files using your preferred native OS editor under the work/
directory, and verify them with Dafny from the terminal that's running the
docker image.

The docker-based command-line Dafny installation above is offered as a
portable, simple way to get started.  There do exist snazzy real-time Dafny
integrations for IDEs (Visual Studio, VSCode) and editors (Emacs, Vim).  You
are certainly welcome to install Dafny natively and integrate it with your
editor if you prefer.

# STOP HERE!

If you're preparing for the summer camp, stop here! The first set of exercises
begins after the first lecture session.

# Working the exercises

The `chapter` directories contain:

* `exercise/*.dfy`: work through these files in order. Instructions appear
  in comments in the file.

* `demo/`: The lecturer will use these files to present new ideas. Feel free to browse them.

* `hint/`: If you get stuck on an exercise, peek into the corresponding hint file. Avoid looking in here if you want to avoid spoilers!

* [exercises.md](exercises.md) is an index of the exercises.

Files in a directory are numbered to indicate the order they're meant to be read.  There is no chapter01-basics/exercise17.dfy because there is a chapter01/demo17.
