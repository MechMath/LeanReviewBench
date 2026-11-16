import dep.equational_theories.Magma
import dep.equational_theories.Equations.Basic
import dep.equational_theories.Equations.Command
import dep.equational_theories.Equations.Eqns1_999
import dep.equational_theories.Equations.Eqns1000_1999
import dep.equational_theories.Equations.Eqns2000_2999
import dep.equational_theories.Equations.Eqns3000_3999
import dep.equational_theories.Equations.Eqns4000_4694
import dep.equational_theories.EquationalResult

/-! List of equational laws being studied -/

/-
The imported files contain the full list of 4694 Equations considered.
Include this file if you want to establish results concerning the entire list of equations.
If you are proving many results about a specific equation of interest, consider transferring it into
`Equations/Basic.lean`.

The equations were enumerated from
`https://github.com/teorth/equational_theories/blob/main/scripts/generate_eqs_list.py`, and can
be described as the set of all equational laws involving at most four magma operations, up to
symmetry and relabeling.

See `Equations/Command.lean` for the definition of the `equation` command.
-/
