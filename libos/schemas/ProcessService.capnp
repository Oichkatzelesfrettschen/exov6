@0x9b9b9b9b9b9b9b9b;

interface ProcessService {
  fork  @0 () -> (childPid :UInt64);
  exec  @1 (path :Text, argv :List(Text)) -> ();
  wait  @2 (pid :UInt64) -> (status :Int32);
  kill  @3 (pid :UInt64, sig :UInt32) -> ();
}
