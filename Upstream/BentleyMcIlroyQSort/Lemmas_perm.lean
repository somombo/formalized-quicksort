import Upstream.Init.Ord
import Upstream.Init.PermStabalizing
import Upstream.BentleyMcIlroyQSort.Basic

open Vector Partition bentleyMcIlroy move_pivots_back

variable [Ord α]
set_option linter.unusedSectionVars false

theorem move_p_back.permStabilizing {n : Nat} {left right p k : Nat} {arr : Vector α n} {j : Nat} {hjr : j < right} {hp : p < n} {hr : right < n} :
    left ≤ k → k ≤ p → p ≤ right + 1 → left + p ≤ j + k + 1 → j ≤ right → PermStabilizing' left right (move_p_back hr hp k arr j hjr).1 arr := by
  intro hleft hkp hpr hlpj hjright
  induction k, arr, j, hjr using move_p_back.induct (hr := hr) (hp := hp) (p := p) with
  | case1 k arr j hjr h ih =>
    unfold move_p_back; simp [h]
    apply PermStabilizing'.trans
    · apply ih <;> omega
    · apply swap_permStabilizing' <;> omega
  | case2 k arr j hjr h =>
    unfold move_p_back; simp [h]
    apply PermStabilizing'.refl

theorem move_q_forward.permStabilizing {n : Nat} {left right q k : Nat} {arr : Vector α n} {i i' : Nat} {hkq : q + 1 ≤ k} {hli : left < i}
    {hi'q : i' ≤ q + 1} {hieqk_invar : i = k - (q + 1) + i'} {hr : right < n} :
    left ≤ q + 1 → q < right → left ≤ i → PermStabilizing' left right (move_q_forward hr hi'q k arr i hkq hli hieqk_invar).1 arr := by
  intro hlq hqr hleft
  induction k, arr, i, hkq, hli, hieqk_invar using move_q_forward.induct (hr := hr) (hi'q := hi'q) with
  | case1 k arr hkq h hli ih =>
    unfold move_q_forward; simp [h]
    apply PermStabilizing'.trans
    · apply ih <;> omega
    · apply swap_permStabilizing' <;> omega
  | case2 k arr hkq h hli =>
    unfold move_q_forward; simp [h]
    apply PermStabilizing'.refl



theorem classic.loop.permStabilizing {n : Nat} {left right : Nat}
    {hr : right < n} {pivot : α}
    (arr : Vector α n) (i j p q : Nat)
    (hpi : p ≤ i) (hqr : q < right) (hli : left < i) (hij : i ≤ j + 1) (hjr : j < right) (hjq : j ≤ q)
    (halgep : ¬lt pivot arr[p - 1] = true) (haqltp : ¬lt arr[q + 1] pivot = true) :
    left + 1 ≤ p → p ≤ right + 1 → left ≤ q + 1 →
    PermStabilizing' left right (classic.loop left right hr (by omega) pivot arr i j p q hpi hqr hli hij hjr hjq halgep haqltp).val.arr' arr := by
  induction arr, i, j, p, q, hpi, hqr, hli, hij, hjr, hjq, halgep, haqltp using classic.loop.induct (left := left) (right := right) (hr := hr) (hl := by omega) (pivot := pivot) with
  | case1 arr i j p q hpi hqr hli hij hjr hjq halgep haqltp j' hj'1 hj'2 hj'3 hjpiva eq_j hjpiva2 i' hi'1 hi'2 hi'3 hapivi eq_i hapivi2 h hqsimp hpsimp arr' hlt4 hlt5 ih =>
    intro hlp hpr hlq
    unfold classic.loop
    simp only [eq_j, eq_i]
    dsimp [arr'] at *
    simp_all
    apply PermStabilizing'.trans
    · apply ih <;> omega
    · apply swap_permStabilizing' <;> omega
  | case2 arr i j p q hpi hqr hli hij hjr hjq halgep haqltp j' hj'1 hj'2 hj'3 hjpiva eq_j hjpiva2 i' hi'1 hi'2 hi'3 hapivi eq_i hapivi2 h hqsimp hpsimp arr' hlt4 hlt5 arr'' ih =>
    intro hlp hpr hlq
    unfold classic.loop
    simp only [eq_j, eq_i]
    dsimp [arr', arr''] at *
    simp_all
    apply PermStabilizing'.trans
    · apply ih <;> omega
    · apply PermStabilizing'.trans
      · apply swap_permStabilizing' <;> omega
      · apply swap_permStabilizing' <;> omega
  | case3 arr i j p q hpi hqr hli hij hjr hjq halgep haqltp j' hj'1 hj'2 hj'3 hjpiva eq_j hjpiva2 i' hi'1 hi'2 hi'3 hapivi eq_i hapivi2 h hqsimp hpsimp arr' hlt4 arr'' hlt5 ih =>
    intro hlp hpr hlq
    unfold classic.loop
    simp only [eq_j, eq_i]
    dsimp [arr', arr''] at *
    simp_all
    apply PermStabilizing'.trans
    · apply ih <;> omega
    · apply PermStabilizing'.trans
      · apply swap_permStabilizing' <;> omega
      · apply swap_permStabilizing' <;> omega
  | case4 arr i j p q hpi hqr hli hij hjr hjq halgep haqltp j' hj'1 hj'2 hj'3 hjpiva eq_j hjpiva2 i' hi'1 hi'2 hi'3 hapivi eq_i hapivi2 h hqsimp hpsimp arr' hlt4 arr'' hlt5 arr''' ih =>
    intro hlp hpr hlq
    unfold classic.loop
    simp only [eq_j, eq_i]
    dsimp [arr', arr'', arr'''] at *
    simp_all
    apply PermStabilizing'.trans
    · apply ih <;> omega
    · apply PermStabilizing'.trans
      · apply swap_permStabilizing' <;> omega
      · apply PermStabilizing'.trans
        · apply swap_permStabilizing' <;> omega
        · apply swap_permStabilizing' <;> omega
  | case5 arr i j p q hpi hqr hli hij hjr hjq halgep haqltp j' hj'1 hj'2 hj'3 hjpiva eq_j hjpiva2 i' hi'1 hi'2 hi'3 hapivi eq_i hapivi2 h1 hp h2 arr'' j'' hj'' eq_p arr''' i'' hi'' eq_q =>
    intro hlp hpr hlq
    unfold classic.loop
    simp only [eq_j, eq_i, eq_p, eq_q, dif_neg h1, dif_pos h2]
    apply PermStabilizing'.trans (as₂ := arr'')
    · have hli_q : left < i' := by omega
      have hi'q_q : i' ≤ q + 1 := hi'3
      have hkq_q : q + 1 ≤ q + 1 := by omega
      have hinv_q : i' = q + 1 - (q + 1) + i' := by omega
      have hlefti_q : left ≤ i' := by omega
      have h_q := move_q_forward.permStabilizing (left := left) (right := right) (arr := arr'') (i := i') (k := q + 1) (i' := i') (q := q) (hr := hr) (hli := hli_q) (hi'q := hi'q_q) (hkq := hkq_q) (hieqk_invar := hinv_q) hlq hqr hlefti_q
      have eq_q_fst : (move_q_forward hr hi'q_q (q + 1) arr'' i' hkq_q hli_q hinv_q).fst = arr''' := congrArg Prod.fst eq_q
      rw [eq_q_fst] at h_q
      exact h_q
    · have hlk_p : left ≤ left + 1 := by omega
      have hkp_p : left + 1 ≤ p := hlp
      have hlpj_p : left + p ≤ j' + (left + 1) + 1 := by omega
      have hjr_p : j' ≤ right := by omega
      have h_p := move_p_back.permStabilizing (left := left) (right := right) (arr := arr) (j := j') (k := left + 1) (p := p) (hr := hr) (hp := hp) (hjr := by omega) hlk_p hkp_p hpr hlpj_p hjr_p
      have eq_p_fst : (move_p_back hr hp (left + 1) arr j' (by omega)).fst = arr'' := congrArg Prod.fst eq_p
      rw [eq_p_fst] at h_p
      exact h_p
  | case6 arr i j p q hpi hqr hli hij hjr hjq halgep haqltp j' hj'1 hj'2 hj'3 hjpiva eq_j hjpiva2 i' hi'1 hi'2 hi'3 hapivi eq_i hapivi2 h1 hp h2 arr'' j'' hj'' eq_p arr''' i'' hi'' eq_q =>
    intro hlp hpr hlq
    unfold classic.loop
    simp only [eq_j, eq_i, eq_p, eq_q, dif_neg h1, dif_neg h2]
    apply PermStabilizing'.trans (as₂ := arr'')
    · have hli_q : left < i' + 1 := by omega
      have hi'q_q : i' + 1 ≤ q + 1 := by omega
      have hkq_q : q + 1 ≤ q + 1 := by omega
      have hinv_q : i' + 1 = q + 1 - (q + 1) + (i' + 1) := by omega
      have hlefti_q : left ≤ i' + 1 := by omega
      have h_q := move_q_forward.permStabilizing (left := left) (right := right) (arr := arr'') (i := i' + 1) (k := q + 1) (i' := i' + 1) (q := q) (hr := hr) (hli := hli_q) (hi'q := hi'q_q) (hkq := hkq_q) (hieqk_invar := hinv_q) hlq hqr hlefti_q
      have eq_q_fst : (move_q_forward hr hi'q_q (q + 1) arr'' (i' + 1) hkq_q hli_q hinv_q).fst = arr''' := congrArg Prod.fst eq_q
      rw [eq_q_fst] at h_q
      exact h_q
    · have hlk_p : left ≤ left + 1 := by omega
      have hkp_p : left + 1 ≤ p := hlp
      have hlpj_p : left + p ≤ (j' - 1) + (left + 1) + 1 := by omega
      have hjr_p : j' - 1 ≤ right := by omega
      have h_p := move_p_back.permStabilizing (left := left) (right := right) (arr := arr) (j := j' - 1) (k := left + 1) (p := p) (hr := hr) (hp := hp) (hjr := by omega) hlk_p hkp_p hpr hlpj_p hjr_p
      have eq_p_fst : (move_p_back hr hp (left + 1) arr (j' - 1) (by omega)).fst = arr'' := congrArg Prod.fst eq_p
      rw [eq_p_fst] at h_p
      exact h_p


theorem eager.loop.permStabilizing {n : Nat} {left right : Nat}
    {hlr : left < right} {hr : right < n} {pivot : α}
    (arr : Vector α n) (i j p q : Nat)
    (hli : left < i) (hij : i ≤ j + 1) (hjr : j < right) (hpi : p ≤ i) (hqr : q < right) (hjq : j ≤ q) :
    left + 1 ≤ p → p ≤ right + 1 → left ≤ q + 1 →
    PermStabilizing' left right (eager.loop left right hlr hr pivot arr i j p q hli hij hjr hpi hqr hjq).val.arr' arr := by
  induction arr, i, j, p, q, hli, hij, hjr, hpi, hqr, hjq using eager.loop.induct (left := left) (right := right) (hr := hr) (hlr := hlr) (pivot := pivot) with
  | case1 arr i j p q hli hij hjr hpi hqr hjq hp h1 arr'' j'' hi''r heq1 arr''' i'' hli'' heq2 =>
    intro hlp hpr hlq
    unfold eager.loop
    simp only [heq1, heq2, dif_pos h1]
    apply PermStabilizing'.trans (as₂ := arr'')
    · have hli_q : left < i := by omega
      have hi'q_q : i ≤ q + 1 := by omega
      have hkq_q : q + 1 ≤ q + 1 := by omega
      have hinv_q : i = q + 1 - (q + 1) + i := by omega
      have hlefti_q : left ≤ i := by omega
      have h_q := move_q_forward.permStabilizing (left := left) (right := right) (arr := arr'') (i := i) (k := q + 1) (i' := i) (q := q) (hr := hr) (hli := hli_q) (hi'q := hi'q_q) (hkq := hkq_q) (hieqk_invar := hinv_q) hlq hqr hlefti_q
      have eq_q_fst : (move_q_forward hr hi'q_q (q + 1) arr'' i hkq_q hli_q hinv_q).fst = arr''' := congrArg Prod.fst heq2
      rw [eq_q_fst] at h_q
      exact h_q
    · have hlk_p : left ≤ left + 1 := by omega
      have hkp_p : left + 1 ≤ p := hlp
      have hlpj_p : left + p ≤ j + (left + 1) + 1 := by omega
      have hjr_p : j ≤ right := by omega
      have h_p := move_p_back.permStabilizing (left := left) (right := right) (arr := arr) (j := j) (k := left + 1) (p := p) (hr := hr) (hp := hp) (hjr := by omega) hlk_p hkp_p hpr hlpj_p hjr_p
      have eq_p_fst : (move_p_back hr hp (left + 1) arr j (by omega)).fst = arr'' := congrArg Prod.fst heq1
      rw [eq_p_fst] at h_p
      exact h_p
  | case2 arr i j p q hli hij hjr hpi hqr hjq hp h1 h2 ih =>
    intro hlp hpr hlq
    unfold eager.loop
    simp_all
  | case3 arr i j p q hli hij hjr hpi hqr hjq hp h1 h2 h3 ih =>
    intro hlp hpr hlq
    unfold eager.loop
    simp_all
  | case4 arr i j p q hli hij hjr hpi hqr hjq hp h1 h2 h3 h4 arr' h5 h6 ih =>
    intro hlp hpr hlq
    unfold eager.loop
    dsimp [arr'] at *
    repeat (split <;> try simp_all <;> try omega)
    apply PermStabilizing'.trans
    · apply ih <;> omega
    · apply swap_permStabilizing' <;> omega
  | case5 arr i j p q hli hij hjr hpi hqr hjq hp h1 h2 h3 h4 arr' h5 h6 arr'' ih =>
    intro hlp hpr hlq
    unfold eager.loop
    dsimp [arr', arr''] at *
    repeat (split <;> try simp_all <;> try omega)
    apply PermStabilizing'.trans
    · apply ih <;> omega
    · apply PermStabilizing'.trans
      · apply swap_permStabilizing' <;> omega
      · apply swap_permStabilizing' <;> omega
  | case6 arr i j p q hli hij hjr hpi hqr hjq hp h1 h2 h3 h4 arr' h5 arr'' h6 ih =>
    intro hlp hpr hlq
    unfold eager.loop
    dsimp [arr', arr''] at *
    repeat (split <;> try simp_all <;> try omega)
    apply PermStabilizing'.trans
    · apply ih <;> omega
    · apply PermStabilizing'.trans
      · apply swap_permStabilizing' <;> omega
      · apply swap_permStabilizing' <;> omega
  | case7 arr i j p q hli hij hjr hpi hqr hjq hp h1 h2 h3 h4 arr' h5 arr'' h6 arr''' ih =>
    intro hlp hpr hlq
    change ¬lt (arr.swap i j)[i] pivot = true at h5
    change ¬lt pivot ((arr.swap i j).swap p i)[j] = true at h6
    simp [Vector.swap] at h5 h6
    unfold eager.loop
    repeat (split <;> try simp_all <;> try omega)
    apply PermStabilizing'.trans
    · apply ih <;> omega
    · apply PermStabilizing'.trans
      · apply swap_permStabilizing' <;> omega
      · apply PermStabilizing'.trans
        · apply swap_permStabilizing' <;> omega
        · apply swap_permStabilizing' <;> omega
  | case8 arr i j p q hli hij hjr hpi hqr hjq hp h1 h2 h3 h4 arr'' j'' hi''r heq1 arr''' i'' hli'' heq2 =>
    intro hlp hpr hlq
    unfold eager.loop
    simp_all
    apply PermStabilizing'.trans (as₂ := arr'')
    · have hli_q : left < i + 1 := by omega
      have hi'q_q : i + 1 ≤ q + 1 := by omega
      have hkq_q : q + 1 ≤ q + 1 := by omega
      have hinv_q : i + 1 = q + 1 - (q + 1) + (i + 1) := by omega
      have hlefti_q : left ≤ i + 1 := by omega
      have h_q := move_q_forward.permStabilizing (left := left) (right := right) (arr := arr'') (i := i + 1) (k := q + 1) (i' := i + 1) (q := q) (hr := hr) (hli := hli_q) (hi'q := hi'q_q) (hkq := hkq_q) (hieqk_invar := hinv_q) hlq hqr hlefti_q
      have eq_q_fst : (move_q_forward hr hi'q_q (q + 1) arr'' (i + 1) hkq_q hli_q hinv_q).fst = arr''' := congrArg Prod.fst heq2
      rw [eq_q_fst] at h_q
      exact h_q
    · have hlk_p : left ≤ left + 1 := by omega
      have hkp_p : left + 1 ≤ p := hlp
      have hlpj_p : left + p ≤ (j - 1) + (left + 1) + 1 := by omega
      have hjr_p : j - 1 ≤ right := by omega
      have h_p := move_p_back.permStabilizing (left := left) (right := right) (arr := arr) (j := j - 1) (k := left + 1) (p := p) (hr := hr) (hp := hp) (hjr := by omega) hlk_p hkp_p hpr hlpj_p hjr_p
      have eq_p_fst : (move_p_back hr hp (left + 1) arr (j - 1) (by omega)).fst = arr'' := congrArg Prod.fst heq1
      rw [eq_p_fst] at h_p
      exact h_p
