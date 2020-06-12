# dgranges

This is a D clone of the [cgranges](https://github.com/lh3/cgranges)
algorithm based of the C++ version.

Documentation, tests, benchmarks, and modularization are coming!

This implementation will be used for the
[biofast](https://github.com/lh3/biofast) benchmark suite. 

## Build

```
ldc2 -O3 -release -flto=full -of=dgranges ./source/app.d

# Or
dub build --release --compiler lcd2

```
