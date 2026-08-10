import Upstream.BentleyMcIlroyQSort.Basic
import Upstream.Init.RangeHas

namespace Partition.bentleyMcIlroy.move_pivots_back
open Vector
variable [Ord α]

theorem move_p_back_preserves {n : Nat} {left right p k : Nat} {arr : Vector α n} {j : Nat} {hjr : j < right} {hp : p < n} {hr : right < n} {pivot : α}
  {j_orig : Nat} (hj_orig : j ≤ j_orig) (H_left_le_k : left ≤ k) (H_p_le : p ≤ j_orig + 1) (H_inv : left + p ≤ j + k + 1)
  (H : ∀ (x : Fin n), left ≤ x.val → x.val ≤ j_orig → ¬lt pivot arr[x]) :
  ∀ (x : Fin n), left ≤ x.val → x.val ≤ (move_p_back hr hp k arr j hjr).2.val → ¬lt pivot (move_p_back hr hp k arr j hjr).1[x] := by
  induction k, arr, j, hjr using move_p_back.induct (hr := hr) (hp := hp) (p := p) with
  | case1 k arr j hjr h ih =>
    intro x hx1 hx2
    rw [move_p_back]
    rw [move_p_back] at hx2
    simp only [h, dite_true]
    simp only [h, dite_true] at hx2
    have H_ih := ih (by omega) (by omega) (by omega) (fun y hy1 hy2 => ?inner) x hx1 hx2
    exact H_ih
    case inner =>
      if hyk : y.val = k then
        have : (arr.swap k j (by omega) (by omega))[y] = arr[j] := by
          simp [hyk, Vector.getElem_swap_left]
        rw [this]
        exact H ⟨j, by omega⟩ (by show left ≤ j; omega) (by show j ≤ j_orig; omega)
      else if hyj : y.val = j then
        have : (arr.swap k j (by omega) (by omega))[y] = arr[k] := by
          simp [hyj, Vector.getElem_swap_right]
        rw [this]
        exact H ⟨k, by omega⟩ (by show left ≤ k; omega) (by show k ≤ j_orig; omega)
      else
        have : (arr.swap k j (by omega) (by omega))[y] = arr[y] := by
          apply Vector.getElem_swap_of_ne
          · exact hyk
          · exact hyj
        rw [this]
        exact H y hy1 hy2
  | case2 k arr j hjr h =>
    unfold move_p_back; simp [h]
    intro x hx1 hx2
    simpa using H x hx1 (by omega)

omit [Ord α] in
private theorem move_p_back_fills_aux {n right p k j dest top : Nat}
    {arr : Vector α n} {hjr : j < right} {hp : p < n} {hr : right < n}
    {pred : α → Prop}
    (hkp : k ≤ p) (hdest : 0 < dest)
    (hrel : dest + (p - k) = j + 1)
    (hsource : RangeHas n (pred arr[·]) k p)
    (hfilled : RangeHas n (pred arr[·]) (j + 1) top)
    (hoverlap : RangeHas n (pred arr[·]) dest p) :
    RangeHas n (pred (move_p_back hr hp k arr j hjr).1[·])
        ((move_p_back hr hp k arr j hjr).2.val + 1) top ∧
      RangeHas n (pred (move_p_back hr hp k arr j hjr).1[·]) dest p := by
  induction k, arr, j, hjr using move_p_back.induct (hr := hr) (hp := hp) with
  | case1 k arr j hjr h ih =>
      rw [move_p_back]
      simp only [h, dite_true]
      have hkn : k < n := Nat.lt_trans h hp
      have hjn : j < n := Nat.lt_trans hjr hr
      have hsubpos : 0 < p - k := Nat.sub_pos_of_lt h
      have hdj : dest ≤ j := by omega
      have hjpos : 0 < j := by omega
      have hjpred : j - 1 + 1 = j := by omega
      have hkp_succ : k + 1 ≤ p := by omega
      have hsub_k := Nat.sub_add_cancel hkp
      have hsub_succ := Nat.sub_add_cancel hkp_succ
      have hlen_succ : p - (k + 1) + 1 = p - k := by omega
      have hrel_succ : dest + (p - (k + 1)) = j - 1 + 1 := by omega
      let arr' := arr.swap k j hkn hjn
      have hsource' : RangeHas n (pred arr'[·]) (k + 1) p := by
        intro x hx1 hx2
        if hxj : x.val = j then
          have heq : arr'[x] = arr[k] := by
            simp only [arr', hxj, Fin.getElem_fin, Vector.getElem_swap_right]
          rw [heq]
          exact hsource ⟨k, hkn⟩ (Nat.le_refl k) h
        else
          have hxk : x.val ≠ k := by omega
          have heq : arr'[x] = arr[x] := by
            apply Vector.getElem_swap_of_ne
            · exact hxk
            · exact hxj
          rw [heq]
          exact hsource x (by omega) hx2
      have hfilled' : RangeHas n (pred arr'[·]) (j - 1 + 1) top := by
        intro x hx1 hx2
        if hxj : x.val = j then
          have heq : arr'[x] = arr[k] := by
            simp only [arr', hxj, Fin.getElem_fin, Vector.getElem_swap_right]
          rw [heq]
          exact hsource ⟨k, hkn⟩ (Nat.le_refl k) h
        else if hxk : x.val = k then
          have heq : arr'[x] = arr[j] := by
            simp only [arr', hxk, Fin.getElem_fin, Vector.getElem_swap_left]
          rw [heq]
          have hjle : j ≤ x.val := by rw [← hjpred]; exact hx1
          have hjk : j < k := by omega
          exact hoverlap ⟨j, hjn⟩ hdj (Nat.lt_trans hjk h)
        else
          have heq : arr'[x] = arr[x] := by
            apply Vector.getElem_swap_of_ne
            · exact hxk
            · exact hxj
          rw [heq]
          exact hfilled x (by omega) hx2
      have hoverlap' : RangeHas n (pred arr'[·]) dest p := by
        intro x hx1 hx2
        if hxk : x.val = k then
          have heq : arr'[x] = arr[j] := by
            simp only [arr', hxk, Fin.getElem_fin, Vector.getElem_swap_left]
          rw [heq]
          have hjp : j < p := by
            have hdk : dest ≤ k := by omega
            have hjp' : j + 1 ≤ p := by
              calc
                j + 1 = dest + (p - k) := hrel.symm
                _ ≤ k + (p - k) := Nat.add_le_add_right hdk (p - k)
                _ = p := by
                  rw [Nat.add_comm]
                  exact Nat.sub_add_cancel hkp
            omega
          exact hoverlap ⟨j, hjn⟩ hdj hjp
        else if hxj : x.val = j then
          have heq : arr'[x] = arr[k] := by
            simp only [arr', hxj, Fin.getElem_fin, Vector.getElem_swap_right]
          rw [heq]
          exact hsource ⟨k, hkn⟩ (Nat.le_refl k) h
        else
          have heq : arr'[x] = arr[x] := by
            apply Vector.getElem_swap_of_ne
            · exact hxk
            · exact hxj
          rw [heq]
          exact hoverlap x hx1 hx2
      exact ih hkp_succ hrel_succ hsource' hfilled' hoverlap'
  | case2 k arr j hjr h =>
      rw [move_p_back]
      simp only [h, dite_false]
      have hkp_eq : k = p := by omega
      subst k
      simp only [Nat.sub_self, Nat.add_zero] at hrel
      constructor
      · simpa only [hrel] using hfilled
      · exact hoverlap

omit [Ord α] in
theorem move_p_back_fills {n right p k j : Nat}
    {arr : Vector α n} {hjr : j < right} {hp : p < n} {hr : right < n}
    {pred : α → Prop}
    (hkpos : 0 < k) (hkp : k ≤ p) (hpj : p ≤ j + 1)
    (hsource : RangeHas n (pred arr[·]) k p) :
    RangeHas n (pred (move_p_back hr hp k arr j hjr).1[·])
      ((move_p_back hr hp k arr j hjr).2.val + 1) (j + 1) := by
  let dest := j + 1 - (p - k)
  have hlen : p - k ≤ j + 1 := Nat.le_trans (Nat.sub_le p k) hpj
  have hrel : dest + (p - k) = j + 1 := by
    exact Nat.sub_add_cancel hlen
  have hsub := Nat.sub_add_cancel hkp
  have hkdest : k ≤ dest := by omega
  have hdest : 0 < dest := Nat.lt_of_lt_of_le hkpos hkdest
  have hoverlap : RangeHas n (pred arr[·]) dest p :=
    RangeHas.mono hsource hkdest (Nat.le_refl p)
  exact (move_p_back_fills_aux hkp hdest hrel hsource
    (RangeHas.refl (j + 1)) hoverlap).1

omit [Ord α] in
theorem move_p_back_eq_after {n right p k j jOrig : Nat}
    {arr : Vector α n} {hjr : j < right} {hp : p < n} {hr : right < n}
    (hjj : j ≤ jOrig) (hpj : p ≤ jOrig + 1)
    (x : Fin n) (hx : jOrig < x.val) :
    (move_p_back hr hp k arr j hjr).1[x] = arr[x] := by
  induction k, arr, j, hjr using move_p_back.induct (hr := hr) (hp := hp) with
  | case1 k arr j hjr h ih =>
      rw [move_p_back]
      simp only [h, dite_true]
      rw [ih (by omega)]
      simpa only [Fin.getElem_fin] using
        (Vector.getElem_swap_of_ne (xs := arr) (i := k) (j := j)
          (k := x.val) (by omega) (by omega))
  | case2 k arr j hjr h =>
      rw [move_p_back]
      simp only [h, dite_false]

set_option linter.unusedVariables false in
theorem move_q_forward_preserves {n : Nat} {left right q k : Nat} {arr : Vector α n} {i : Nat} {hli : left < i} {hr : right < n} {pivot : α}
  {i' : Nat} (hi'q : i' ≤ q + 1) (hkq : q + 1 ≤ k) (hieqk_invar : i = k - (q + 1) + i')
  {i_orig : Nat} (hi_orig : i_orig ≤ i) (hk_le : i_orig ≤ k) (H_i_orig_le_q : i_orig ≤ q + 1)
  (H : ∀ (x : Fin n), i_orig ≤ x.val → x.val ≤ right → ¬lt arr[x] pivot) :
  ∀ (x : Fin n), (move_q_forward hr hi'q k arr i hkq hli hieqk_invar).2.val ≤ x.val → x.val ≤ right → ¬lt (move_q_forward hr hi'q k arr i hkq hli hieqk_invar).1[x] pivot := by
  induction k, arr, i, hkq, hli, hieqk_invar using move_q_forward.induct (hr := hr) (hi'q := hi'q) with
  | case1 k arr hkq h hli ih =>
    intro x hx1 hx2
    rw [move_q_forward]
    rw [move_q_forward] at hx1
    simp only [h, dite_true]
    simp only [h, dite_true] at hx1
    have H_ih := ih (by omega) (by omega) (fun y hy1 hy2 => ?inner) x hx1 hx2
    exact H_ih
    case inner =>
      if hyk : y.val = k then
        have : (arr.swap k (k - (q + 1) + i') (by omega) (by omega))[y] = arr[k - (q + 1) + i'] := by
          simp [hyk, Vector.getElem_swap_left]
        rw [this]
        exact H ⟨k - (q + 1) + i', by omega⟩ (by show i_orig ≤ k - (q + 1) + i'; omega) (by show k - (q + 1) + i' ≤ right; omega)
      else if hyi : y.val = k - (q + 1) + i' then
        have : (arr.swap k (k - (q + 1) + i') (by omega) (by omega))[y] = arr[k] := by
          simp [hyi, Vector.getElem_swap_right]
        rw [this]
        exact H ⟨k, by omega⟩ (by show i_orig ≤ k; omega) (by show k ≤ right; omega)
      else
        have : (arr.swap k (k - (q + 1) + i') (by omega) (by omega))[y] = arr[y] := by
          apply Vector.getElem_swap_of_ne
          · exact hyk
          · exact hyi
        rw [this]
        exact H y hy1 hy2
  | case2 k arr hkq h hli =>
    unfold move_q_forward; simp [h]
    intro x hx1 hx2
    simpa using H x (by omega) hx2

omit [Ord α] in
theorem move_q_forward_eq_before {n : Nat} {left right q k : Nat}
    {arr : Vector α n} {i i' : Nat} {hkq : q + 1 ≤ k} {hli : left < i}
    {hi'q : i' ≤ q + 1} {hieqk : i = k - (q + 1) + i'} {hr : right < n}
    (x : Fin n) (hx : x.val < i) :
    (move_q_forward hr hi'q k arr i hkq hli hieqk).1[x] = arr[x] := by
  induction k, arr, i, hkq, hli, hieqk using
      move_q_forward.induct (hr := hr) (hi'q := hi'q) with
  | case1 k arr hkq h hli ih =>
      rw [move_q_forward]
      simp only [h, dite_true]
      rw [ih (by omega)]
      simpa only [Fin.getElem_fin] using
        (Vector.getElem_swap_of_ne (xs := arr) (i := k) (j := k - (q + 1) + i')
          (k := x.val) (by omega) (by omega))
  | case2 k arr hkq h hli =>
      rw [move_q_forward]
      simp only [h, dite_false]

omit [Ord α] in
theorem move_q_forward_fills {n : Nat} {left right q k : Nat}
    {arr : Vector α n} {i i' : Nat} {hkq : q + 1 ≤ k} {hli : left < i}
    {hi'q : i' ≤ q + 1} {hieqk : i = k - (q + 1) + i'} {hr : right < n}
    {pred : α → Prop}
    (hsource : RangeHas n (pred arr[·]) k right) :
    RangeHas n (pred (move_q_forward hr hi'q k arr i hkq hli hieqk).1[·])
      i (move_q_forward hr hi'q k arr i hkq hli hieqk).2.val := by
  induction k, arr, i, hkq, hli, hieqk using
      move_q_forward.induct (hr := hr) (hi'q := hi'q) with
  | case1 k arr hkq h hli ih =>
      rw [move_q_forward]
      simp only [h, dite_true]
      have hdest_le_k : k - (q + 1) + i' ≤ k := by
        calc
          k - (q + 1) + i' ≤ k - (q + 1) + (q + 1) :=
            Nat.add_le_add_left hi'q (k - (q + 1))
          _ = k := Nat.sub_add_cancel hkq
      have hstep : k + 1 - (q + 1) = k - (q + 1) + 1 := by
        simpa only [Nat.succ_eq_add_one] using Nat.succ_sub hkq
      have hki : k < n := by omega
      have hdesti : k - (q + 1) + i' < n := Nat.lt_of_le_of_lt hdest_le_k hki
      have hkq_succ : q + 1 ≤ k + 1 := Nat.le_trans hkq (Nat.le_succ k)
      have hli_succ : left < k - (q + 1) + i' + 1 := Nat.lt_succ_of_lt hli
      have hieq_succ :
          k - (q + 1) + i' + 1 = k + 1 - (q + 1) + i' := by
        rw [hstep]
        omega
      apply RangeHas.prepend
      · have hsrc := hsource ⟨k, hki⟩ (Nat.le_refl k) h
        have hframe := move_q_forward_eq_before
          (hr := hr) (hi'q := hi'q) (k := k + 1)
          (arr := arr.swap k (k - (q + 1) + i') hki hdesti)
          (i := k - (q + 1) + i' + 1) (hkq := hkq_succ) (hli := hli_succ)
          (hieqk := hieq_succ) ⟨k - (q + 1) + i', hdesti⟩
          (Nat.lt_succ_self _)
        rw [hframe]
        simpa only [Fin.getElem_fin, Vector.getElem_swap_right] using hsrc
      · apply ih
        intro x hx1 hx2
        have hxk : x.val ≠ k := by omega
        have hxi : x.val ≠ k - (q + 1) + i' := by omega
        have heq :
            (arr.swap k (k - (q + 1) + i') hki hdesti)[x] = arr[x] := by
          apply Vector.getElem_swap_of_ne
          · exact hxk
          · exact hxi
        rw [heq]
        exact hsource x (by omega) hx2
  | case2 k arr hkq h hli =>
      rw [move_q_forward]
      simp only [h, dite_false]
      exact RangeHas.refl _

omit [Ord α] in
theorem move_q_forward_preserves_range {n : Nat} {left right q k top : Nat}
    {arr : Vector α n} {i i' : Nat} {hkq : q + 1 ≤ k} {hli : left < i}
    {hi'q : i' ≤ q + 1} {hieqk : i = k - (q + 1) + i'} {hr : right < n}
    {pred : α → Prop}
    (hrt : right ≤ top) (hpred : RangeHas n (pred arr[·]) i top) :
    RangeHas n (pred (move_q_forward hr hi'q k arr i hkq hli hieqk).1[·])
      (move_q_forward hr hi'q k arr i hkq hli hieqk).2.val top := by
  induction k, arr, i, hkq, hli, hieqk using
      move_q_forward.induct (hr := hr) (hi'q := hi'q) with
  | case1 k arr hkq h hli ih =>
      rw [move_q_forward]
      simp only [h, dite_true]
      have hdest_le_k : k - (q + 1) + i' ≤ k := by
        calc
          k - (q + 1) + i' ≤ k - (q + 1) + (q + 1) :=
            Nat.add_le_add_left hi'q (k - (q + 1))
          _ = k := Nat.sub_add_cancel hkq
      have hdest_right : k - (q + 1) + i' < right :=
        Nat.lt_of_le_of_lt hdest_le_k h
      have hdest_n : k - (q + 1) + i' < n := Nat.lt_trans hdest_right hr
      apply ih
      intro x hx1 hx2
      if hxk : x.val = k then
        have heq :
            (arr.swap k (k - (q + 1) + i') (by omega) (by omega))[x] =
              arr[k - (q + 1) + i'] := by
          simp only [hxk, Fin.getElem_fin, Vector.getElem_swap_left]
        rw [heq]
        exact hpred ⟨k - (q + 1) + i', hdest_n⟩ (Nat.le_refl _)
          (Nat.lt_of_lt_of_le hdest_right hrt)
      else
        have hxi : x.val ≠ k - (q + 1) + i' := by omega
        have heq :
            (arr.swap k (k - (q + 1) + i') (by omega) (by omega))[x] = arr[x] := by
          apply Vector.getElem_swap_of_ne
          · exact hxk
          · exact hxi
        rw [heq]
        exact hpred x (by omega) hx2
  | case2 k arr hkq h hli =>
      rw [move_q_forward]
      simp only [h, dite_false]
      exact hpred

end Partition.bentleyMcIlroy.move_pivots_back
