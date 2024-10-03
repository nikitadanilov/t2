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

_TBD_.

Transportability
----------------

All tests are done on Ubuntu, any Linux version should be all right. There is a
macos (Darwin) port, but it lacks some features, like asynchronous IO.

Limitations
-----------

- Only C bindings exist.

- The implementation of trasnactions supports integration with an external
  trasnaction engine, so that t2 can be used as a part of large system (_e.g._,
  as a meta-data store in a file-system server), but this has never been tried
  and will most likely require some additional coding.
  
- Darwin port is slow.
