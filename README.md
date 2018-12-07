# ZCache
Use the cache-z.h file for ZCache and skewed-associative cache and the Cache-baseline.h for the 4-way set-associative cache. 
The cache-z-4-16-par.c implements the ZCache with 2-level replacement whereas the cache-z-4-52.c implements the ZCache with 3-level replacement.
The code is written for the SimpleScalar simulator suite, and specifically for sim-outorder simulator.
Modify the make file to include the appropriate cache.h and cache.c files from this repository before compiling sim-outorder and running the simulations.
As an alternative, you can create backups of the default cache.h and cache.c files in the simulator suite and rename the appropriate files from this repository to cache.h and cache.c before compiling and running sim-outorder.
Follow the standard procedure to run the sim-outorder simulator, once compiled.
