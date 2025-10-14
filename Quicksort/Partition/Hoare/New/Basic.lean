import Quicksort.Partition.Init.Basic

namespace Partition

variable [Ord α]

instance : Nonempty ([Ord α] → {n j left : Nat} → α → Vector α n → (jval : Nat) → jval ≤ j → left ≤ jval → j < n → { j' // j' ≤ j }) :=
  ⟨fun _ _ jval _ _ _ => ⟨jval, by grind⟩⟩

set_option warn.sorry false

@[inline]
def hoare.new.loop.while_j' (pivot : α)  (arr : Vector α n) (jval : Nat)  (hjj : jval ≤ j)
    (hxj : left ≤ jval) (hj : j < n) : { j' : Nat // j' ≤ j }:=
  if h' : /- jval ≠ left ∧ -/ lt pivot arr[jval] then
    have _ : jval ≠ left := sorry
    while_j' (left:=left) pivot  arr (jval - 1) (by omega) (by omega) (by omega)
  else
    ⟨jval, by grind⟩
partial_fixpoint
-- termination_by jval
-- decreasing_by
--   have hterm_strong_precon : ∃ (left : Nat) (hj' : left < n), left ≤ jval ∧ ¬ lt pivot arr[left] := sorry
--   grind

@[inline]
def hoare.new.loop.while_i' (pivot : α)  (arr : Vector α n) (ival : Nat) (hli : left < ival) (hxi : ival ≤ right)
    (hr : right < n)  : { i' : Nat // left < i' } :=
  -- NOTEvv: @somombo: ival = right → lt pivot arr[ival] if lt is asymmetric
  if _ : /- ival ≠ right ∧ -/  lt arr[ival] pivot then
    have _ : ival ≠ right := sorry
    while_i' (right:=right) pivot  arr (ival + 1)  (by omega) (by omega) hr
  else
    ⟨ival, hli⟩


open Vector in
@[inline]
def hoare.new (arr : Vector α n) (left : Nat) (right : Nat) (hlr : left < right)
    (hr : right < n) : { x : Partition α n  // left < x.i' ∧ x.j' < right } :=
  have hl : left < n := by omega

  let rec @[specialize] loop (pivot : α) (arr : Vector α n) (i j : Nat) /- (hj : j < n) -/ (hli : left < i)
      (hir : i ≤ right) (hlj : left ≤ j) (hjr : j < right) : { x : Partition α n  // left < x.i' ∧ x.j' < right } :=

    let ⟨j', _⟩ := new.loop.while_j' pivot  arr j  Nat.le.refl hlj (by omega)
    let ⟨i', _⟩ := new.loop.while_i' pivot  arr i  hli hir hr

    if _ : i' < j' then
      let arr' := arr.swap i' j'
      loop pivot arr' (i' + 1) (j' - 1) (by grind)  (by grind) (by grind) (by grind)
    else if _ : j' < i' then
      ⟨⟨arr, j', i'⟩, by grind, by grind⟩
    else
      ⟨⟨arr, j' - 1, i' + 1⟩, by grind, by grind⟩
  -- termination_by j + 1 - i
  -- decreasing_by
  --   change j' - 1 + 1 - (i' + 1) < j + 1 - i
  --   -- have hii__ : i ≤ i' := sorry
  --   omega
  -- partial_fixpoint

  let mid := left + ((right - left)/2)
  have hm : mid < n := by omega
  let arr_ := arr
    |> (maybeSwap · ⟨left, hl⟩ ⟨mid, hm⟩)
    |> (maybeSwap · ⟨left, hl⟩ ⟨right, hr⟩)
    |> (maybeSwap · ⟨mid, hm⟩ ⟨right, hr⟩)

  let pivot := arr_[mid]
  loop pivot arr_ (left + 1) (right - 1) (by omega) (by omega) (by omega) (by omega)




























-- theorem hoare.new.loop.while_j'_lt_n
--     {pivot : α} {arr : Vector α n}
--     -- (hterm_strong_precon : ∃ (left : Nat) (hj' : left < n), left ≤ jval ∧ ¬ lt pivot arr[left])
--     :
--     while_j' pivot arr jval hj < n := by
--   unfold while_j'
--   if h' : lt pivot arr[jval] then
--     simp [h']
--     apply while_j'_lt_n
--     -- grind
--   else
--     grind
-- termination_by jval
-- decreasing_by
--   rename_i e this a ; clear _x this a
--   simp_all
--   grind



-- theorem hoare.new.loop.while_j'_ltj
--     {left right : Nat} {hr : right < n} {hl : left < n} {pivot : α}
--     {arr : Vector α n} {i j : Nat} {hjr : j < right} {hli : left < i}
--     {jval : Nat} (hj : jval < n) (hxj : left ≤ jval) (hjj : jval ≤ j)

--     -- {pivot : α} {arr : Vector α n}
--     (hterm_strong_precon : ¬ lt pivot arr[left]) :
--     while_j' pivot arr jval hj ≤ j := by
--   unfold while_j'
--   if h' : lt pivot arr[jval] then
--     simp_all [-hterm_strong_precon]

--     have _ : jval ≠ left := /- by omega -/
--       (h' |> show ¬lt pivot arr[jval] by simpa only [·])
--     exact while_j'_ltj (left:=left) (right:=right) (pivot:=pivot) (arr:=arr) (hli:=by omega) (hjr:=by omega) (hl:=by omega) (hr:=by omega)
--       (jval:=jval-1) (hj:= by omega)
--       (by grind) (by omega) (by grind)
--   else
--     simp [*]
-- -- termination_by jval
-- -- decreasing_by grind
