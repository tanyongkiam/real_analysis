open realTheory limTheory

val _ = new_theory "real_analysis";

val _ = ParseExtras.tight_equality()

val _ = set_trace"Goalstack.print_goal_at_top"0 handle HOL_ERR _ => set_trace"goalstack print goal at top"0

Theorem real_induction
  `(∀x. a ≤ x ∧ x ≤ b ⇒
    (∀y. a ≤ y ∧ y < x ⇒ P y) ⇒
      P x ∧
      (P x ∧ x < b ⇒ ∃e. 0 < e ∧ ∀y. x < y ∧ y < x + e ⇒ P y)) ⇒
    ∀x. a ≤ x ∧ x ≤ b ⇒ P x`
  (
  simp[METIS_PROVE [] ``A ∧ (A ∧ B ⇒ C) ⇔ A ∧ (B ⇒ C)``]>>
  strip_tac>>
  CCONTR_TAC>>
  qabbrev_tac`pred = λx. a ≤ x ∧ x ≤ b ∧ ¬ P x`>>
  (* at least one counter example *)
  `?zz. pred zz` by
    (fs[Abbr`pred`]>>metis_tac[])>>
  qpat_x_assum`~Q` kall_tac>>
  first_x_assum(qspec_then `inf pred` mp_tac)>>
  impl_keep_tac>- (
    rw[]
    >-
      (match_mp_tac REAL_IMP_LE_INF>>
      metis_tac[])
    >>
      match_mp_tac REAL_IMP_INF_LE>>
      rw[]>>
      metis_tac[])>>
  impl_tac>- (
    rw[]>>
    CCONTR_TAC>>
    `inf pred ≤ y` by
      (match_mp_tac REAL_IMP_INF_LE>>
      rw[]
      >-
        metis_tac[]
      >>
        fs[Abbr`pred`]>>
        metis_tac[REAL_LE_LT,REAL_LT_TRANS])>>
    metis_tac[REAL_NOT_LT])>>
  strip_tac>>
  Cases_on `inf pred < b`
  >- (
    res_tac>>
    `inf pred + e ≤ inf pred` by (
      match_mp_tac REAL_IMP_LE_INF>>
      rw[]>- metis_tac[]>>
      simp[GSYM REAL_NOT_LT]>>
      strip_tac>>
      fs[]>>
      first_x_assum(qspec_then`x` mp_tac)>>
      impl_tac>- (
        rw[]>>metis_tac[REAL_INF_LE,REAL_LE_LT])>>
      fs[Abbr`pred`])>>
    `inf pred < inf pred + e` by fs[REAL_LT_ADDR]>>
    metis_tac[REAL_NOT_LE])
  >>
    `inf pred = b` by metis_tac[REAL_LE_LT]>>
    `zz < b` by metis_tac[REAL_LE_LT,Abbr`pred`] >>
    `inf pred ≤ zz` by (
      match_mp_tac REAL_IMP_INF_LE>>
      rw[]
      >-
        metis_tac[]>>
      qexists_tac`zz`>>fs[])>>
    metis_tac[REAL_NOT_LT]);

(* Function continuous at x is locally bounded in some interval about x *)
Theorem CONT_LOCAL_BOUNDED
  `$contl f x ⇒
  ∃M d.
    0 < d ∧
    ∀y.
    x-d < y ∧ y < x+d ⇒ f y ≤ M`
  (rw[CONTL_LIM,LIM]>>
  first_x_assum(qspec_then`1` assume_tac)>>fs[]>>
  qexists_tac`f x + 1`>>
  qexists_tac`d`>>
  rw[]>>
  Cases_on`x=y`
  >-
    simp[REAL_LE_ADDR]>>
  first_x_assum(qspec_then`y` mp_tac)>>
  impl_tac>- (
    rw[]>-
      simp[GSYM ABS_NZ]>>
    simp[GSYM ABS_BETWEEN] )
  >>
  simp[Once ABS_SUB]>>
  strip_tac>> imp_res_tac ABS_BOUND>>
  fs[REAL_LT_LE]);

Theorem CONT_BOUNDED
  `∀f a b.
    (∀ x. a ≤ x ∧ x ≤ b ⇒ $contl f x)
    ⇒
    ∃M.
      ∀x. a ≤ x ∧ x ≤ b ⇒ f x ≤ M`
  (rw[]>>
  reverse (Cases_on` a ≤ b`)
  >- (
    qexists_tac`0`>>rw[]>>
    metis_tac[REAL_NOT_LE,REAL_LE_TRANS])>>
  qabbrev_tac`P = λy. ∃M. ∀x. a ≤ x ∧ x ≤ y ⇒ f x ≤ M`>>
  qsuff_tac`P b`
  >-
    fs[Abbr`P`]>>
  mp_tac real_induction>>
  impl_tac>- (
    rw[]
    >- (
      last_x_assum(qspec_then`x` assume_tac)>>rfs[]>>
      imp_res_tac CONT_LOCAL_BOUNDED>>
      Cases_on`a <= x-d`
      >-
        (last_x_assum(qspec_then`x-d` mp_tac)>>fs[]>>
        impl_tac>-
          simp[REAL_LT_SUB_RADD,REAL_LT_ADDR]>>
        rw[Abbr`P`]>>
        qexists_tac`max M M'`>>rw[]
        >- (
          Cases_on`x' <= x - d`
          >-
            metis_tac[REAL_LE_MAX2,REAL_LE_TRANS]
          >>
          fs[REAL_NOT_LE]>>
          `x' < x+d` by
            metis_tac[REAL_LT_ADDR,REAL_LE_LT,REAL_LT_TRANS]>>
          metis_tac[REAL_LE_MAX1,REAL_LE_TRANS]))
      >>
        fs[REAL_NOT_LE]>>
        rw[Abbr`P`]>>
        metis_tac[REAL_LT_ADDR,REAL_LE_LT,REAL_LT_TRANS])
    >>
      last_x_assum(qspec_then`x` assume_tac)>>rfs[]>>
      imp_res_tac CONT_LOCAL_BOUNDED>>
      qexists_tac`d`>>simp[]>>
      rw[Abbr`P`]>>
      fs[]>>
      qexists_tac`max M M'`>>rw[]>>
      Cases_on`x' ≤ x`
      >- (
        last_x_assum(qspec_then`x'` kall_tac)>>
        last_x_assum(qspec_then`x'` mp_tac)>>fs[]>>
        metis_tac[REAL_LE_MAX2,REAL_LE_TRANS])
      >>
      fs[REAL_NOT_LE]>>
      first_x_assum(qspec_then`x'` mp_tac)>>
      impl_tac>-
        metis_tac[REAL_LT_ADDR,REAL_LE_LT,REAL_LT_TRANS,REAL_LT_SUB_RADD]>>
       metis_tac[REAL_LE_MAX1,REAL_LE_TRANS])>>
  metis_tac[REAL_LE_REFL]);

val _ = export_theory();
