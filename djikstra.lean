
structure Graph where
  mat : List (List Nat)
  wf  : ∀ i : Fin mat.length, mat[i].length = mat.length

instance : Inhabited Graph := ⟨[], fun i => by nomatch i⟩

opaque g : Graph

abbrev Vertex := Fin g.mat.length

def Graph.weight (u v : Vertex) : Nat :=
  g.mat[u][v]'(by rw [g.wf u]; exact v.isLt)


notation "d[" i ", " j "]" => Graph.weight i j

axiom hg₀ : 0 < g.mat.length
axiom hg₁ : ∀ i j : Vertex, i ≠ j → d[i, j] > 0
axiom hg₂ : ∀ i j : Vertex, i = j → d[i, j] = 0

opaque INF : Nat

axiom hINF : 0 < INF

instance : Inhabited (Fin g.mat.length) := ⟨0, hg₀⟩

opaque SOURCE : Vertex

structure ShortestPath where
  list : List Nat
  len : list.length = g.mat.length

def ShortestPath.get (SP : ShortestPath) (v : Vertex) :=
  SP.list[v.val]'(SP.len.symm ▸ v.isLt)

instance : Inhabited ShortestPath := ⟨List.replicate g.mat.length INF, by simp⟩

variable (SP : ShortestPath)

notation SP "[" v "]" => ShortestPath.get SP v

def djikstra_spec : Prop × Prop × Prop :=
  ⟨SP[SOURCE] = 0,
  ∀ z y : Vertex, (SP[y] < INF ∧ d[y, z] < INF) → SP[z] ≤ SP[y] + d[y, z],
  ∀ z : Vertex, z ≠ SOURCE ∧ SP[z] < INF → ∃ y : Vertex, y ≠ z ∧ SP[z] = SP[y] + d[y, z]⟩
