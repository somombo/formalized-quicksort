
-- import Std.Time.DateTime.Timestamp
import Std.Time


-- (dbgTraceIfShared s!"as={as}\n" as.qsort)



def timeAx (ax : IO α) : IO (Std.Time.Duration × α)  := do
  let start ← Std.Time.Timestamp.now
  let a ←  ax
  let dur ← Std.Time.Timestamp.since start
  return (dur, a)


-- #check Std.Time.ZonedDateTime.toISO8601String
-- #check Std.Time.PlainDateTime.ofTimestampAssumingUTC
-- -- def now_std_str (t : Std.Time.Timestamp) : IO String := do
-- --   Std.Time.PlainDateTime.ofTimestampAssumingUTC t |>.toTimestampWithZone

-- #eval do

--   return (← Std.Time.ZonedDateTime.now).format "uuuu-MM-dd'T'HH:mm:ssXXX"
--   -- return t.format "uuuu-MM-dd'T'HH:mm:ssXXX"
