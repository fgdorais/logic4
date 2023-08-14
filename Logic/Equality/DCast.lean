import Logic.Basic
import Logic.Equality.DEq

/-- Dependent type casting -/
def dcast {motive : α → Sort _} (h : a = b) (t : motive a) : motive b := Eq.ndrec t h

@[simp_cast] theorem Eq.ndrec_eq_dcast {motive : α → Sort _} (h : a = b) (t : motive a) : Eq.ndrec t h = dcast h t := rfl

namespace Logic

@[simp_cast] theorem cast_eq_dcast (h : α = β) (t : α) : cast h t = dcast (motive:=id) h t := rfl

@[simp_cast] theorem dcast_id {motive : α → Sort _} (h : a = a) (t : motive a) : dcast h t = t := by
  cases h; rfl

@[simp_cast] theorem dcast_comp {motive : α → Sort _} (hab : a = b) (hbc : b = c) (t : motive a) : dcast hbc (dcast hab t) = dcast (Eq.trans hab hbc) t := by
  cases hab; rfl

@[simp_cast] theorem deq_dcast_left {motive : α → Sort _} (h : a = b) (t : motive a) (u : motive c) : DEq (dcast h t) u ↔ DEq t u := by
  cases h; exact Iff.rfl

@[simp_cast] theorem deq_dcast_right {motive : α → Sort _} (h : b = c) (t : motive a) (u : motive b) : DEq t (dcast h u) ↔ DEq t u := by
  cases h; exact Iff.rfl

@[simp_cast] theorem heq_dcast_left {motive : α → Sort _} (h : a = b) (t : motive a) (u : motive c) : HEq (dcast h t) u ↔ HEq t u := by
  cases h; exact Iff.rfl

@[simp_cast] theorem heq_dcast_right {motive : α → Sort _} (h : b = c) (t : motive a) (u : motive b) : HEq t (dcast h u) ↔ HEq t u := by
  cases h; exact Iff.rfl

set_option hygiene false in
macro "simp_cast" : tactic =>
  `(tactic| ((try apply eq_of_heq); simp only [simp_cast]; (try apply heq_of_eq)))
