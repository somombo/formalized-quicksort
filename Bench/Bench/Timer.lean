
-- import Std.Time.DateTime.Timestamp
import Std.Time


-- (dbgTraceIfShared s!"as={as}\n" as.qsort)

def timeAx (ax : IO α) : IO (Std.Time.Duration × α)  := do
  let start ← Std.Time.Timestamp.now
  let a ←  ax
  let dur ← Std.Time.Timestamp.since start
  return (dur, a)
