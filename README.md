Overview
--------

t2 is a local key-value store library based on B-trees. An interface is
provided to create trees and then to insert a key-value record, delete the
record with a given key, look up the record with a given key and iterate through
the records. B-trees can be stored in a file or on a block
device. Write-ahead-logging is used to guarantee atomicity of individual tree
operations (insertions and deletions).

Fast lookup path is fully lockless (as a matter of fact, it does not use any
atomic instructions) and scales as concurrency levels increase. In general t2
performance compares favourably to rocksdb, lmdb and `std::map`.

Build
-----

[build](https://github.com/nikitadanilov/t2/blob/master/build) script manages build process.

To install the packages necessary for build (this needs to be done once):

    $ ./build -S

To build a debug version (this is the default, when no options are given):

    $ ./build -d

To build an optimised version:

    $ ./build -f

The last 2 commands produce:

- `t2.o`: an object file that can be linked in your application;
- `ut`: a unit-test binary;
- `bn`: a benchmarking executable.

Benchmarks
----------

The plots below are made by `./benchmarks` script, which runs a "typical" set of
workloads against t2 and rocksdb (additionally C++ `std::map` is used in some
cases). Warning: the script takes a lot of time (a few hours) to complete, in
part because it, by default, repeats each experiment 5 times (see `nr` variable).

Configuration:

    16-core i7-12650H, 32GB memory, Kingston 501b ssd

Insert 50M records:

![insert 50M records](https://github.com/nikitadanilov/t2/blob/master/doc/images/insert-50M.png?raw=true)

Each record has a random key of between 8 and 16 bytes, a random value between
10 and 20 bytes. 100 threads inserting records, 500K records per thread. The graph
plots the progress.

Now that the key-value store is populated, benchmark lookups at various concurrency levels:

![lookup 50M records](https://github.com/nikitadanilov/t2/blob/master/doc/images/lookup-50M.png?raw=true)

Next, iterate over the keys: create 50K cursors, each doing 1000 iterations
(50M iterations total with varying concurrency levels).

Currently, cursors in t2 use fairly standard B-tree locking. This is sugnificantly slower than lockless lookup:

![iterate over 50M records](https://github.com/nikitadanilov/t2/blob/master/doc/images/iterations-50M.png?raw=true)

Delete the records:

![delete 50M records](https://github.com/nikitadanilov/t2/blob/master/doc/images/deletes-50M.png?raw=true)

Finally, benchmark concurrent insertion of random and sequential keys in a freshly re-initialised key-value store:

![insert random keys](https://github.com/nikitadanilov/t2/blob/master/doc/images/insert-rnd.png?raw=true)


![insert sequential keys](https://github.com/nikitadanilov/t2/blob/master/doc/images/insert-seq.png?raw=true)

Transportability
----------------

All tests are done on Ubuntu, any Linux version should be all right. t2 compiles
on macos (Darwin), but it lacks some features, like asynchronous IO there.

Limitations
-----------

- Only C bindings exist.

- The implementation of trasnactions supports integration with an external
  trasnaction engine, so that t2 can be used as a part of large system (_e.g._,
  as a meta-data store in a file-system server), but this has never been tried
  and will most likely require some additional coding.
  
- Darwin port is slow.
