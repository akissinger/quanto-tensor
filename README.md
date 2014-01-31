Installation
============

To run, you need [Isabelle 2013-2](http://isabelle.in.tum.de/) and [Nominal2](http://isabelle.in.tum.de/nominal/).

The theory files expect to find the Nominal2 theories in a folder called nominal2. So, unzip the Nominal2 distro, rename the folder to nominal2 then clone quanto-tensor next door:

    tar xzf Nominal2-Isabelle-XX.tar.gz
    mv Nominal2-Isabelle-XX nominal2
    git clone https://github.com/akissinger/quanto-tensor.git

The theory files should then run when you open them in Isabelle. Be aware that when you first open any of the files, it takes quite a while to check because Nominal2 needs to build, but after that they should be pretty zippy.