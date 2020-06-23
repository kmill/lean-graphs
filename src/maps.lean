-- combinatorial maps

--import data.multiset
import data.list.perm
import data.fintype.basic
import data.equiv.basic
import group_theory.perm.cycles
import myequiv
import tactic

namespace maps

open function
open equiv

universe u

-- A two-dimension combinatorial map is a collection D of darts, a
-- permutation σ whose orbits correspond to vertices, and a
-- fixed-point-free involution τ whose orbits correspond to edges.  We
-- think of σ as giving the next dart counterclockwise around an edge,
-- and τ as giving the opposite dart of an edge. (Note: this
-- definition excludes disjoint isolated vertices.)
--
-- We only care about the case where the orbits of σ are finite, but
-- we do not require it in the definition.
structure cmap (D : Type u) :=
(σ : perm D) (τ : perm D) (τ_inv : involutive τ) (τ_fp_free : ¬has_fixed_point τ)

namespace cmap
variables {D D' : Type u}

-- The next dart counter-clockwise around a face
@[simp] def ϕ (m : cmap D) : perm D := equiv.trans m.σ.symm m.τ

-- We only will care about the case of equivalences, but in this
-- definition a homomorphism of combinatorial maps is sort of like a
-- branched covering map of surfaces branched over the vertices.
def hom (m : cmap D) (m' : cmap D') (f : D → D') :=
(f ∘ m.σ = m'.σ ∘ f) ∧ (f ∘ m.τ = m'.τ ∘ f)

lemma hom_inv_is_hom (m : cmap D) (m' : cmap D') (f : equiv D D') (h : hom m m' f) : hom m' m f.symm :=
begin
  split,
  calc f.symm ∘ m'.σ = f.symm ∘ m'.σ ∘ id : by refl
                 ... = f.symm ∘ m'.σ ∘ (f ∘ f.symm) : by rw ←self_comp_symm
                 ... = f.symm ∘ (m'.σ ∘ f) ∘ f.symm : by refl
                 ... = f.symm ∘ (f ∘ m.σ) ∘ f.symm : by rw ← h.1
                 ... = (f.symm ∘ f) ∘ m.σ ∘ f.symm : by refl
                 ... = id ∘ m.σ ∘ f.symm : by rw symm_comp_self
                 ... = m.σ ∘ f.symm : by refl,
  calc f.symm ∘ m'.τ = f.symm ∘ m'.τ ∘ id : by refl
                 ... = f.symm ∘ m'.τ ∘ (f ∘ f.symm) : by rw ←self_comp_symm
                 ... = f.symm ∘ (m'.τ ∘ f) ∘ f.symm : by refl
                 ... = f.symm ∘ (f ∘ m.τ) ∘ f.symm : by rw ← h.2
                 ... = (f.symm ∘ f) ∘ m.τ ∘ f.symm : by refl
                 ... = id ∘ m.τ ∘ f.symm : by rw symm_comp_self
                 ... = m.τ ∘ f.symm : by refl,
end

-- In light of `hom_inv_is_hom`, we define an equivalence of maps as
-- an equivalence of their dart sets that is a homomorphism.
def equiv_maps (m : cmap D) (m' : cmap D') (f : equiv D D') := hom m m' f

-- We define the opposite of a map to be the one which reverses the identities of the darts on each edge
def opp (m : cmap D) : cmap D := ⟨equiv.trans (equiv.trans m.τ m.σ) m.τ, m.τ, m.τ_inv, m.τ_fp_free⟩

-- Form the dual map.  This swaps the roles of vertices and faces
def dual (m : cmap D) : cmap D := ⟨m.ϕ, m.τ, m.τ_inv, m.τ_fp_free⟩

lemma double_dual_is_opp (m : cmap D) : m.dual.dual = m.opp :=
begin
  cases m, dsimp [opp, dual], congr,
  calc (m_σ.symm.trans m_τ).symm = m_τ.symm.trans m_σ.symm.symm : by rw equiv.symm_trans_eq_trans_sym
                             ... = m_τ.symm.trans m_σ : by rw equiv.symm_symm
                             ... = m_τ.trans m_σ : by rw equiv.symm_involution m_τ m_τ_inv,
end

-- The opposite of a map (and hence the double dual) is equivalent to the original map.
lemma double_dual (m : cmap D) : ∃ (f : equiv D D), hom m m.opp f :=
begin
  use m.τ,
  split,
  calc m.τ ∘ m.σ = m.τ ∘ m.σ ∘ id : by refl
             ... = m.τ ∘ m.σ ∘ (m.τ ∘ m.τ) : by rw ←equiv.involution_comp_involution m.τ m.τ_inv
             ... = m.opp.σ ∘ m.τ : by refl,
  refl,
end

-- A "dual homomorphism" is a homomorphism that sends vertices to
-- faces and faces to vertices.  The entire point of this definition
-- is purely for `dual_dequiv`.
def dhom (m : cmap D) (m' : cmap D') (f : D → D') :=
(f ∘ m.σ = m'.ϕ ∘ f) ∧ (f ∘ m.τ = m'.τ ∘ f)

-- This is a dhom from a map to its dual.  See `dual_dequiv`.
def to_dual (m : cmap D) : D → D := m.τ

-- A map and its dual are dual equivalent (hence the name)
lemma dual_dequiv (m : cmap D) : dhom m m.dual (to_dual m) :=
begin
  split, ext, simp [dual, to_dual],
  refl,
end


@[reducible] def vertex_setoid (m : cmap D) := perm.psetoid m.σ
@[reducible] def edge_setoid (m : cmap D) := perm.psetoid m.τ
@[reducible] def face_setoid (m : cmap D) := perm.psetoid m.ϕ

@[reducible] def vertices (m : cmap D) := quotient (vertex_setoid m)
@[reducible] def edges (m : cmap D) := quotient (edge_setoid m)
@[reducible] def faces (m : cmap D) := quotient (face_setoid m)

-- The vertex at the dart
@[reducible] def dart_vertex (m : cmap D) (d : D) : m.vertices := @quotient.mk _ (vertex_setoid m) d
-- The edge on the the dart
@[reducible] def dart_edge (m : cmap D) (d : D) : m.edges := @quotient.mk _ (edge_setoid m) d
-- The face to the left of the dart.  That is, the one traced out by `m.ϕ`
@[reducible] def dart_face (m : cmap D) (d : D) : m.faces := @quotient.mk _ (face_setoid m) d

-- The degree of a vertex is the number of incident darts.
def vertices.deg {m : cmap D} [fintype D] [decidable_eq D] (v : m.vertices) : ℕ := begin
  dsimp [vertices] at v, induction v,
  exact fintype.card {d | perm.same_cycle m.σ v d},
  simp, congr, ext, change m.σ.same_cycle v_a v_b at v_p,
  split, intro sc1, exact perm.same_cycle.trans _ (perm.same_cycle.symm _ v_p) sc1,
  intro sc2, exact perm.same_cycle.trans _ v_p sc2,
end

def vertices.darts {m : cmap D} (v : m.vertices) := {d : D | m.dart_vertex d = v}

instance vertices.darts.fintype {m : cmap D} [fintype D] [decidable_eq D] (v : m.vertices) : fintype v.darts :=
begin
  induction v,
  change fintype {d : D | @quotient.mk _ (vertex_setoid m) d = @quotient.mk _ (vertex_setoid m) v},
  simp,
  change fintype {d : D | perm.same_cycle m.σ d v},
  apply_instance,
  have h : ∀ d, m.σ.same_cycle d v_a ↔ m.σ.same_cycle d v_b, {
    sorry,
  },
  suggest,
end

def vertices.deg {m : cmap D} [fintype D] [decidable_eq D] (v : m.vertices) : ℕ := fintype.card v.darts

-- Apply m.σ to a dart at a vertex, yielding another dart at the same vertex
def vertices.σ {m : cmap D} (v : m.vertices) : perm v.darts :=
begin
  let f : v.darts → v.darts, {
    rintro ⟨d, hd⟩,
    refine ⟨m.σ d, _⟩,
    simp [vertices.darts] at ⊢ hd,
    rw ←hd, dsimp [dart_vertex],
    apply quotient.sound,
    change perm.same_cycle _ _ _,
    rw ←perm.same_cycle_apply,
  },
  let g : v.darts → v.darts, {
    rintro ⟨d, hd⟩,
    refine ⟨m.σ.symm d, _⟩,
    simp [vertices.darts] at ⊢ hd,
    rw ←hd, dsimp [dart_vertex],
    apply quotient.sound,
    change perm.same_cycle _ _ _,
    rw ←perm.same_cycle_inv_apply,
    rw perm.inv_def,
  },
  use [f,g],
  rintro ⟨d,h⟩, simp [f,g],
  rintro ⟨d,h⟩, simp [f,g],
end



-- Apply m.σ to a dart at a vertex, yielding another dart at the same vertex
def vertices.σ {m : cmap D} (v : m.vertices) (d : v.darts) : v.darts :=
begin
  cases d, refine ⟨m.σ d_val, _⟩,
  simp [vertices.darts] at ⊢ d_property,
  rw ← d_property, dsimp [dart_vertex],
  apply quotient.sound,
  change perm.same_cycle _ _ _,
  rw ←perm.same_cycle_apply,
end

def faces.darts {m : cmap D} (f : m.faces) := {d : D | m.dart_face d = f}

def faces.σ {m : cmap D} (f : m.faces) (d : f.darts) : f.darts :=

def dart_between.helper {m : cmap D} [decidable_eq D] (v : m.vertices) : ℕ → v.darts → v.darts → v.darts → Prop
| 0 _ _ _ := false
| (n+1) dlo dhi d := if dlo = dhi then true else dart_between.helper n (v.σ dlo) dhi d

-- Given three darts dlo, dhi, and d around a given vertex, determines
-- whether d is between dlo and dhi (inclusive), going counterclockwise.
def dart_between {m : cmap D} [fintype D] [decidable_eq D] (v : m.vertices) (dlo dhi d : v.darts) : Prop :=
dart_between.helper v v.deg dlo dhi d

--def vertices.darts_from {m : cmap D} [fintype D] [decidable_eq D] (v : m.vertices) {d : D} (h : v = m.dart_vertex d) : list D :=
--(list.range v.deg).m

-- The number of sides of a given face
def faces.sides {m : cmap D} [fintype D] [decidable_eq D] (f : m.faces) : ℕ := begin
  dsimp [faces] at f, induction f,
  exact fintype.card {d | perm.same_cycle m.ϕ f d},
  simp, congr, ext, change m.ϕ.same_cycle f_a f_b at f_p,
  split, intro sc1, exact perm.same_cycle.trans _ (perm.same_cycle.symm _ f_p) sc1,
  intro sc2, exact perm.same_cycle.trans _ f_p sc2,
end

def dual_vertex_face_equiv (m : cmap D) : m.faces ≃ m.dual.vertices :=
begin
  let f : m.faces → m.dual.vertices := begin
    intro x, induction x, exact m.dual.dart_vertex x,
    change perm.same_cycle _ _ _ at x_p,
    simpa,
  end,
  let g : m.dual.vertices → m.faces := begin
    intro x, induction x, exact m.dart_face x,
    change perm.same_cycle _ _ _ at x_p,
    simpa,
  end,
  use [f, g],
  intro x, induction x, refl, refl,
  intro x, induction x, refl, refl,
end

def dual_edge_edge_equiv (m : cmap D) : m.edges ≃ m.dual.edges :=
begin
  use [id, id],
  intro x, induction x, refl, refl,
  intro x, induction x, refl, refl,
end

-- def opp_vertex_equiv_vertex (m : cmap D) : m.vertices ≃ m.opp.vertices :=
-- ⟨begin
--   dsimp [vertices],
--   intro v, induction v, exact dart_vertex m.opp (m.τ v),
--   simp [dart_vertex],
--   apply quot.sound,
--   simp [perm.same_cycle, opp],
--   rcases v_p with ⟨i,eq⟩, use i, unfold_coes,
-- --  calc (((m.τ.trans m.σ).trans m.τ) ^ i) (m.τ v_a)
-- --         = (m.τ.trans (m.σ ^ i).trans m.τ.symm) (m.τ v_a)
-- --     ... = (m.τ.trans (m.σ ^ i).trans m.τ.symm) (m.τ v_a)
-- end,sorry,sorry,sorry⟩

-- def dual_vertex_face_equiv (m : cmap D) : m.vertices ≃ m.dual.faces :=
-- begin
--   refine ⟨_,_,_,_⟩,
--   dsimp [vertices,faces,dual,vertex_setoid,face_setoid],
-- end


def euler_characteristic (m : cmap D) [fintype D] [decidable_eq D] : ℤ :=
↑(fintype.card m.vertices) - ↑(fintype.card m.edges) + ↑(fintype.card m.faces)

inductive path (m : cmap D) : m.vertices → m.vertices → Type u
| refl {v : m.vertices} : path v v
| edge (d : D) : path (m.dart_vertex d) (m.dart_vertex (m.τ d))
| join {u v w : m.vertices} : path u v → path v w → path u w

def path.symm {m : cmap D} : ∀ {v w : m.vertices}, path m v w → path m w v
| _ _ path.refl := path.refl
| _ _ (path.join p₁ p₂) := path.join p₂.symm p₁.symm
| _ _ (path.edge d) :=
begin
  have h : m.dart_vertex d = m.dart_vertex (m.τ (m.τ d)), rw m.τ_inv d,
  rw h,
  exact path.edge (m.τ d),
end

def path.length {m : cmap D} : ∀{v w : m.vertices}, path m v w → ℕ
| _ _ path.refl := 0
| _ _ (path.edge d) := 1
| _ _ (path.join p1 p2) := p1.length + p2.length

def connected (m : cmap D) (v w : m.vertices) : Prop := nonempty (path m v w)

def connected.setoid (m : cmap D) : setoid m.vertices :=
⟨connected m,
  (λ x, ⟨path.refl⟩),
  (λ x y r, nonempty.rec_on r (λ r', ⟨path.symm r'⟩)),
  (λ x y z r₁ r₂, nonempty.rec_on r₁ (λ r₁', nonempty.rec_on r₂ (λ r₂', ⟨path.join r₁' r₂'⟩)))⟩

def π₀ (m : cmap D) := quotient (connected.setoid m)

def disk (m : cmap D) (v : m.vertices) (n : ℕ) : set m.vertices := {w : m.vertices | ∃ (p : path m v w), p.length ≤ n}

lemma disk.subset (m : cmap D) (v : m.vertices) {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) : m.disk v n₁ ⊆ m.disk v n₂ :=
begin
  rintros v ⟨p, plen⟩,
  exact ⟨p, by linarith⟩,
end

lemma disk.finite_bound (m : cmap D) [fintype D] [decidable_eq D] {v w : m.vertices} (h : m.connected v w)
: w ∈ m.disk v (fintype.card D) :=
begin
  unfreezeI,
  rcases h with ⟨p⟩,
  let lengths := {n | n ≤ p.length ∧ ∃ (q : m.path v w), n = q.length},
  have len_in : p.length ∈ lengths, {
    split, linarith,
    use p,
  },
  have Asup := well_founded.has_min nat.lt_wf lengths ⟨p.length, len_in⟩,
  rcases Asup with ⟨m, m_in, Asup⟩,
  rcases m_in.2 with ⟨q, qlen⟩,
  have hup : q.length ≤ fintype.card D, {
    by_contradiction, push_neg at a,
--    rw qlen at a,
    sorry, --pigeonhole principle
  },
  exact ⟨q, hup⟩,
end

instance disk.decidable_pred (m : cmap D) [fintype D] [decidable_eq D] (v : m.vertices) (n : ℕ) : decidable_pred (m.disk v n) :=
begin
  intro w,
  dunfold disk,
  
end

-- this is the statement that you can do graph searches
instance connected.decidable_rel (m : cmap D) [fintype D] [decidable_eq D] : decidable_rel (connected m) :=
begin
  intros v w,
  let d := m.disk v (fintype.card D),
end

instance π₀.fintype (m : cmap D) [fintype D] [decidable_eq D] : fintype (π₀ m) :=
begin
  have h : decidable_rel (connected.setoid m).r, {
    change decidable_rel (connected m), apply_instance,
  },
  apply @quotient.fintype _ _ (connected.setoid m) h,
end

-- The zeroth Betti number is the number of connected components
def b₀ (m : cmap D) [fintype D] [decidable_eq D] : ℕ := fintype.card (π₀ m)

--def genus (m : cmap D) [fintype D] [decidable_eq D] : ℕ := m.b₀ - m.euler_characteristic/2

end cmap

end maps
