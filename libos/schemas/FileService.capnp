@0xa9a9a9a9a9a9a9a9;

struct Qid {
  path @0 :UInt64;
  version @1 :UInt32;
  type @2 :UInt8;
}

interface NinePSession {
  walk @0 (path :Text) -> (qid :Qid);
  open @1 (qid :Qid, mode :UInt8) -> (fid :UInt64);
  read @2 (fid :UInt64, offset :UInt64, len :UInt32) -> (data :Data);
  write @3 (fid :UInt64, offset :UInt64, data :Data) -> (n :UInt32);
  clunk @4 (fid :UInt64) -> ();
  stat  @5 (fid :UInt64) -> (stat :Data);
}
