import Batteries.Data.Array.Lemmas
import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.ToExpr
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Function
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Cases
import dep.equational_theories.EndToEnd.Basic
import dep.equational_theories.EndToEnd.Certificate
import dep.equational_theories.EndToEnd.Dual
import dep.equational_theories.EndToEnd.Load
import dep.equational_theories.EquationLawConversion
import dep.equational_theories.Equations.Basic
import dep.equational_theories.Equations.Command
import dep.equational_theories.Equations.Eqns1000_1999
import dep.equational_theories.Equations.Eqns1_999
import dep.equational_theories.Equations.Eqns2000_2999
import dep.equational_theories.Equations.Eqns3000_3999
import dep.equational_theories.Equations.Eqns4000_4694
import dep.equational_theories.Equations.LawsComplete
import dep.equational_theories.FreeMagma
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw
import dep.equational_theories.MagmaOp
import dep.equational_theories.ParseImplications
import dep.equational_theories.Preorder
import dep.equational_theories.RArray

namespace EndToEnd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def _root_.EndToEnd.pos3 : RArray EndToEnd.PosFact :=
RArray.branch 1000
  (RArray.branch 500
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2325, conc := 2320, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2325, conc := 2324, proof := sorry })
                      (RArray.leaf { hyp := 2326, conc := 2237, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2327, conc := 2237, proof := sorry })
                      (RArray.leaf { hyp := 2329, conc := 2237, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2330, conc := 2237, proof := sorry })
                      (RArray.leaf { hyp := 2334, conc := 2326, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2335, conc := 2328, proof := sorry })
                      (RArray.leaf { hyp := 2335, conc := 2331, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2335, conc := 2333, proof := sorry })
                      (RArray.leaf { hyp := 2337, conc := 2237, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 232, conc := 231, proof := sorry })
                      (RArray.leaf { hyp := 2339, conc := 2237, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2341, conc := 2340, proof := sorry })
                      (RArray.leaf { hyp := 2345, conc := 2338, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2345, conc := 2341, proof := sorry })
                      (RArray.leaf { hyp := 2345, conc := 2343, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2345, conc := 2344, proof := sorry })
                      (RArray.leaf { hyp := 2346, conc := 2242, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2346, conc := 2336, proof := sorry })
                      (RArray.leaf { hyp := 2349, conc := 2338, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2349, conc := 2347, proof := sorry })
                      (RArray.leaf { hyp := 2350, conc := 2242, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2350, conc := 2329, proof := sorry })
                      (RArray.leaf { hyp := 2353, conc := 2351, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2353, conc := 2352, proof := sorry })
                      (RArray.leaf { hyp := 2354, conc := 2245, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2354, conc := 2326, proof := sorry })
                      (RArray.leaf { hyp := 2354, conc := 2339, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2357, conc := 2355, proof := sorry })
                      (RArray.leaf { hyp := 2357, conc := 2356, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2358, conc := 2342, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2359, conc := 2351, proof := sorry })
                      (RArray.leaf { hyp := 2361, conc := 2351, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2362, conc := 2349, proof := sorry })
                      (RArray.leaf { hyp := 2362, conc := 2359, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2362, conc := 2360, proof := sorry })
                      (RArray.leaf { hyp := 2362, conc := 2361, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2363, conc := 2252, proof := sorry })
                      (RArray.leaf { hyp := 2363, conc := 2289, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2363, conc := 2326, proof := sorry })
                      (RArray.leaf { hyp := 2365, conc := 2327, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2366, conc := 2328, proof := sorry })
                      (RArray.leaf { hyp := 2367, conc := 2252, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2367, conc := 2292, proof := sorry })
                      (RArray.leaf { hyp := 2367, conc := 2329, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2368, conc := 2293, proof := sorry })
                      (RArray.leaf { hyp := 2369, conc := 2292, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2369, conc := 2330, proof := sorry })
                      (RArray.leaf { hyp := 2370, conc := 2331, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2370, conc := 2368, proof := sorry })
                      (RArray.leaf { hyp := 2371, conc := 2255, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2371, conc := 2289, proof := sorry })
                      (RArray.leaf { hyp := 2371, conc := 2329, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2372, conc := 2255, proof := sorry })
                      (RArray.leaf { hyp := 2372, conc := 2290, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2372, conc := 2330, proof := sorry })
                      (RArray.leaf { hyp := 2374, conc := 2331, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2374, conc := 2373, proof := sorry })
                      (RArray.leaf { hyp := 2375, conc := 2295, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2375, conc := 2363, proof := sorry })
                      (RArray.leaf { hyp := 2375, conc := 2367, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2375, conc := 2371, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2376, conc := 2364, proof := sorry })
                      (RArray.leaf { hyp := 2377, conc := 2333, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2378, conc := 2368, proof := sorry })
                      (RArray.leaf { hyp := 236, conc := 229, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 236, conc := 232, proof := sorry })
                      (RArray.leaf { hyp := 236, conc := 234, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 236, conc := 235, proof := sorry })
                      (RArray.leaf { hyp := 2379, conc := 2370, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2380, conc := 2299, proof := sorry })
                      (RArray.leaf { hyp := 2380, conc := 2336, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2382, conc := 2253, proof := sorry })
                      (RArray.leaf { hyp := 2382, conc := 2299, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2383, conc := 2338, proof := sorry })
                      (RArray.leaf { hyp := 2384, conc := 2252, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2384, conc := 2302, proof := sorry })
                      (RArray.leaf { hyp := 2387, conc := 2385, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2387, conc := 2386, proof := sorry })
                      (RArray.leaf { hyp := 2388, conc := 2255, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2388, conc := 2299, proof := sorry })
                      (RArray.leaf { hyp := 2389, conc := 2300, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2391, conc := 2389, proof := sorry })
                      (RArray.leaf { hyp := 2391, conc := 2390, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2392, conc := 2342, proof := sorry })
                      (RArray.leaf { hyp := 2393, conc := 2385, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2395, conc := 2385, proof := sorry })
                      (RArray.leaf { hyp := 2396, conc := 2383, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2396, conc := 2393, proof := sorry })
                      (RArray.leaf { hyp := 2396, conc := 2394, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2396, conc := 2395, proof := sorry })
                      (RArray.leaf { hyp := 2397, conc := 2262, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2397, conc := 2336, proof := sorry })
                      (RArray.leaf { hyp := 2400, conc := 2338, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2401, conc := 2262, proof := sorry })
                      (RArray.leaf { hyp := 2401, conc := 2292, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2404, conc := 2402, proof := sorry })
                      (RArray.leaf { hyp := 2404, conc := 2403, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2405, conc := 2265, proof := sorry })
                      (RArray.leaf { hyp := 2405, conc := 2289, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2405, conc := 2339, proof := sorry })
                      (RArray.leaf { hyp := 2408, conc := 2406, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2408, conc := 2407, proof := sorry })
                      (RArray.leaf { hyp := 2409, conc := 2342, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2410, conc := 2402, proof := sorry })
                      (RArray.leaf { hyp := 2412, conc := 2402, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2413, conc := 2400, proof := sorry })
                      (RArray.leaf { hyp := 2413, conc := 2410, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2413, conc := 2411, proof := sorry })
                      (RArray.leaf { hyp := 2413, conc := 2412, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2414, conc := 2272, proof := sorry })
                      (RArray.leaf { hyp := 2414, conc := 2309, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2414, conc := 2346, proof := sorry })
                      (RArray.leaf { hyp := 2414, conc := 2380, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2414, conc := 2397, proof := sorry })
                      (RArray.leaf { hyp := 2415, conc := 2381, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2416, conc := 2347, proof := sorry })
                      (RArray.leaf { hyp := 2416, conc := 2365, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2416, conc := 2399, proof := sorry })
                      (RArray.leaf { hyp := 2417, conc := 2381, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2418, conc := 2400, proof := sorry })
                      (RArray.leaf { hyp := 240, conc := 238, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 240, conc := 239, proof := sorry })
                      (RArray.leaf { hyp := 2419, conc := 2272, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2419, conc := 2313, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2419, conc := 2367, proof := sorry })
                      (RArray.leaf { hyp := 2419, conc := 2401, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2423, conc := 2370, proof := sorry })
                      (RArray.leaf { hyp := 2423, conc := 2420, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2423, conc := 2421, proof := sorry })
                      (RArray.leaf { hyp := 2423, conc := 2422, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2424, conc := 2276, proof := sorry })
                      (RArray.leaf { hyp := 2424, conc := 2309, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2424, conc := 2350, proof := sorry })
                      (RArray.leaf { hyp := 2424, conc := 2371, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2424, conc := 2388, proof := sorry })
                      (RArray.leaf { hyp := 2428, conc := 2374, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2428, conc := 2391, proof := sorry })
                      (RArray.leaf { hyp := 2428, conc := 2408, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2428, conc := 2425, proof := sorry })
                      (RArray.leaf { hyp := 2428, conc := 2426, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2428, conc := 2427, proof := sorry })
                      (RArray.leaf { hyp := 2429, conc := 2317, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2429, conc := 2354, proof := sorry })
                      (RArray.leaf { hyp := 2429, conc := 2384, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2433, conc := 2366, proof := sorry })
                      (RArray.leaf { hyp := 2433, conc := 2430, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2434, conc := 2392, proof := sorry })
                      (RArray.leaf { hyp := 2434, conc := 2409, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2434, conc := 2419, proof := sorry })
                      (RArray.leaf { hyp := 2435, conc := 2376, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2435, conc := 2415, proof := sorry })
                      (RArray.leaf { hyp := 2435, conc := 2420, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2436, conc := 2377, proof := sorry })
                      (RArray.leaf { hyp := 2437, conc := 2417, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2438, conc := 2378, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2438, conc := 2432, proof := sorry })
                      (RArray.leaf { hyp := 242, conc := 221, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2439, conc := 2379, proof := sorry })
                      (RArray.leaf { hyp := 2439, conc := 2418, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2442, conc := 2440, proof := sorry })
                      (RArray.leaf { hyp := 2443, conc := 2440, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2444, conc := 2441, proof := sorry })
                      (RArray.leaf { hyp := 2446, conc := 2440, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2447, conc := 2441, proof := sorry })
                      (RArray.leaf { hyp := 2448, conc := 2440, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 243, conc := 231, proof := sorry })
                      (RArray.leaf { hyp := 2450, conc := 2441, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2450, conc := 2449, proof := sorry })
                      (RArray.leaf { hyp := 2451, conc := 2442, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2451, conc := 2445, proof := sorry })
                      (RArray.leaf { hyp := 2451, conc := 2448, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2454, conc := 2444, proof := sorry })
                      (RArray.leaf { hyp := 2454, conc := 2450, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2455, conc := 2440, proof := sorry })
                      (RArray.leaf { hyp := 2456, conc := 2440, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2457, conc := 2441, proof := sorry })
                      (RArray.leaf { hyp := 2458, conc := 2440, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 244, conc := 242, proof := sorry })
                      (RArray.leaf { hyp := 244, conc := 243, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2459, conc := 2440, proof := sorry })
                      (RArray.leaf { hyp := 2460, conc := 2441, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2461, conc := 2442, proof := sorry })
                      (RArray.leaf { hyp := 2461, conc := 2455, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2461, conc := 2458, proof := sorry })
                      (RArray.leaf { hyp := 2464, conc := 2460, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2464, conc := 2462, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2465, conc := 2440, proof := sorry })
                      (RArray.leaf { hyp := 2466, conc := 2440, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2467, conc := 2441, proof := sorry })
                      (RArray.leaf { hyp := 2468, conc := 2440, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2469, conc := 2440, proof := sorry })
                      (RArray.leaf { hyp := 2470, conc := 2441, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2471, conc := 2442, proof := sorry })
                      (RArray.leaf { hyp := 2471, conc := 2465, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2471, conc := 2468, proof := sorry })
                      (RArray.leaf { hyp := 2472, conc := 2442, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2472, conc := 2466, proof := sorry })
                      (RArray.leaf { hyp := 2473, conc := 2443, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2473, conc := 2465, proof := sorry })
                      (RArray.leaf { hyp := 2474, conc := 2470, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2474, conc := 2473, proof := sorry })
                      (RArray.leaf { hyp := 2475, conc := 2445, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2475, conc := 2455, proof := sorry })
                      (RArray.leaf { hyp := 2475, conc := 2465, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2478, conc := 2447, proof := sorry })
                      (RArray.leaf { hyp := 2478, conc := 2457, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2478, conc := 2467, proof := sorry })
                      (RArray.leaf { hyp := 246, conc := 231, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2480, conc := 2445, proof := sorry })
                      (RArray.leaf { hyp := 2480, conc := 2459, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2481, conc := 2446, proof := sorry })
                      (RArray.leaf { hyp := 2481, conc := 2458, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2481, conc := 2469, proof := sorry })
                      (RArray.leaf { hyp := 2482, conc := 2470, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2482, conc := 2479, proof := sorry })
                      (RArray.leaf { hyp := 2483, conc := 2448, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2483, conc := 2455, proof := sorry })
                      (RArray.leaf { hyp := 2483, conc := 2468, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2484, conc := 2448, proof := sorry })
                      (RArray.leaf { hyp := 2484, conc := 2456, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2486, conc := 2470, proof := sorry })
                      (RArray.leaf { hyp := 2487, conc := 2451, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2487, conc := 2461, proof := sorry })
                      (RArray.leaf { hyp := 2487, conc := 2471, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2487, conc := 2479, proof := sorry })
                      (RArray.leaf { hyp := 2487, conc := 2483, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2488, conc := 2451, proof := sorry })
                      (RArray.leaf { hyp := 2488, conc := 2462, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2488, conc := 2472, proof := sorry })
                      (RArray.leaf { hyp := 2488, conc := 2480, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 247, conc := 231, proof := sorry })
                      (RArray.leaf { hyp := 2489, conc := 2452, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2490, conc := 2453, proof := sorry })
                      (RArray.leaf { hyp := 2490, conc := 2463, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2490, conc := 2485, proof := sorry })
                      (RArray.leaf { hyp := 2491, conc := 2454, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2491, conc := 2464, proof := sorry })
                      (RArray.leaf { hyp := 2491, conc := 2474, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2491, conc := 2482, proof := sorry })
                      (RArray.leaf { hyp := 2491, conc := 2486, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2492, conc := 2440, proof := sorry })
                      (RArray.leaf { hyp := 2495, conc := 2440, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2496, conc := 2440, proof := sorry })
                      (RArray.leaf { hyp := 248, conc := 246, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 248, conc := 247, proof := sorry })
                      (RArray.leaf { hyp := 2501, conc := 2494, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2501, conc := 2497, proof := sorry })
                      (RArray.leaf { hyp := 2501, conc := 2500, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2502, conc := 2440, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2503, conc := 2440, proof := sorry })
                      (RArray.leaf { hyp := 2504, conc := 2441, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2505, conc := 2440, proof := sorry })
                      (RArray.leaf { hyp := 2507, conc := 2441, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 249, conc := 233, proof := sorry })
                      (RArray.leaf { hyp := 2510, conc := 2502, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2510, conc := 2506, proof := sorry })
                      (RArray.leaf { hyp := 2511, conc := 2504, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2511, conc := 2507, proof := sorry })
                      (RArray.leaf { hyp := 2511, conc := 2509, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2512, conc := 2445, proof := sorry })
                      (RArray.leaf { hyp := 2512, conc := 2502, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2515, conc := 2494, proof := sorry })
                      (RArray.leaf { hyp := 2515, conc := 2513, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2515, conc := 2514, proof := sorry })
                      (RArray.leaf { hyp := 2516, conc := 2445, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2516, conc := 2505, proof := sorry })
                      (RArray.leaf { hyp := 2519, conc := 2497, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2519, conc := 2517, proof := sorry })
                      (RArray.leaf { hyp := 2521, conc := 2506, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2523, conc := 2494, proof := sorry })
                      (RArray.leaf { hyp := 2523, conc := 2522, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2524, conc := 2508, proof := sorry })
                      (RArray.leaf { hyp := 2524, conc := 2520, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2525, conc := 2499, proof := sorry })
                      (RArray.leaf { hyp := 2526, conc := 2509, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2526, conc := 2514, proof := sorry })
                      (RArray.leaf { hyp := 2527, conc := 2500, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2528, conc := 2501, proof := sorry })
                      (RArray.leaf { hyp := 2528, conc := 2511, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2528, conc := 2515, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2528, conc := 2519, proof := sorry })
                      (RArray.leaf { hyp := 2528, conc := 2523, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2528, conc := 2525, proof := sorry })
                      (RArray.leaf { hyp := 2528, conc := 2526, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2528, conc := 2527, proof := sorry })
                      (RArray.leaf { hyp := 251, conc := 247, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2529, conc := 2440, proof := sorry })
                      (RArray.leaf { hyp := 2530, conc := 2440, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2532, conc := 2440, proof := sorry })
                      (RArray.leaf { hyp := 2533, conc := 2440, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2537, conc := 2443, proof := sorry })
                      (RArray.leaf { hyp := 2537, conc := 2529, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2537, conc := 2533, proof := sorry })
                      (RArray.leaf { hyp := 2538, conc := 2531, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2538, conc := 2534, proof := sorry })
                      (RArray.leaf { hyp := 252, conc := 247, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2539, conc := 2440, proof := sorry })
                      (RArray.leaf { hyp := 2540, conc := 2440, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2542, conc := 2440, proof := sorry })
                      (RArray.leaf { hyp := 2544, conc := 2543, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2546, conc := 2543, proof := sorry })
                      (RArray.leaf { hyp := 2547, conc := 2543, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2548, conc := 2541, proof := sorry })
                      (RArray.leaf { hyp := 2548, conc := 2544, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2548, conc := 2546, proof := sorry })
                      (RArray.leaf { hyp := 2548, conc := 2547, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 253, conc := 226, proof := sorry })
                      (RArray.leaf { hyp := 253, conc := 236, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 253, conc := 240, proof := sorry })
                      (RArray.leaf { hyp := 253, conc := 244, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 253, conc := 248, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 253, conc := 250, proof := sorry })
                      (RArray.leaf { hyp := 253, conc := 251, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 253, conc := 252, proof := sorry })
                      (RArray.leaf { hyp := 2549, conc := 2445, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2552, conc := 2541, proof := sorry })
                      (RArray.leaf { hyp := 2552, conc := 2550, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2553, conc := 2445, proof := sorry })
                      (RArray.leaf { hyp := 2553, conc := 2532, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2554, conc := 2543, proof := sorry })
                      (RArray.leaf { hyp := 2555, conc := 2543, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2556, conc := 2554, proof := sorry })
                      (RArray.leaf { hyp := 2556, conc := 2555, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2557, conc := 2448, proof := sorry })
                      (RArray.leaf { hyp := 2557, conc := 2529, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2558, conc := 2530, proof := sorry })
                      (RArray.leaf { hyp := 2558, conc := 2543, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2559, conc := 2543, proof := sorry })
                      (RArray.leaf { hyp := 2560, conc := 2558, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2560, conc := 2559, proof := sorry })
                      (RArray.leaf { hyp := 2561, conc := 2535, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2561, conc := 2545, proof := sorry })
                      (RArray.leaf { hyp := 2563, conc := 2559, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2564, conc := 2559, proof := sorry })
                      (RArray.leaf { hyp := 2565, conc := 2538, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2565, conc := 2548, proof := sorry })
                      (RArray.leaf { hyp := 2565, conc := 2556, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2565, conc := 2560, proof := sorry })
                      (RArray.leaf { hyp := 2565, conc := 2562, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2565, conc := 2563, proof := sorry })
                      (RArray.leaf { hyp := 2565, conc := 2564, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2566, conc := 2455, proof := sorry })
                      (RArray.leaf { hyp := 2566, conc := 2492, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2566, conc := 2529, proof := sorry })
                      (RArray.leaf { hyp := 2569, conc := 2531, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2569, conc := 2568, proof := sorry })
                      (RArray.leaf { hyp := 2570, conc := 2455, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2570, conc := 2532, proof := sorry })
                      (RArray.leaf { hyp := 2572, conc := 2456, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2572, conc := 2495, proof := sorry })
                      (RArray.leaf { hyp := 2572, conc := 2533, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2573, conc := 2534, proof := sorry })
                      (RArray.leaf { hyp := 2575, conc := 2458, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2575, conc := 2493, proof := sorry })
                      (RArray.leaf { hyp := 2575, conc := 2533, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2577, conc := 2534, proof := sorry })
                      (RArray.leaf { hyp := 2578, conc := 2574, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2579, conc := 2499, proof := sorry })
                      (RArray.leaf { hyp := 2580, conc := 2536, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2581, conc := 2500, proof := sorry })
                      (RArray.leaf { hyp := 2581, conc := 2571, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2582, conc := 2573, proof := sorry })
                      (RArray.leaf { hyp := 2582, conc := 2577, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2582, conc := 2579, proof := sorry })
                      (RArray.leaf { hyp := 2583, conc := 2455, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2583, conc := 2502, proof := sorry })
                      (RArray.leaf { hyp := 2585, conc := 2502, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2586, conc := 2541, proof := sorry })
                      (RArray.leaf { hyp := 2587, conc := 2455, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2587, conc := 2505, proof := sorry })
                      (RArray.leaf { hyp := 2587, conc := 2542, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2588, conc := 2543, proof := sorry })
                      (RArray.leaf { hyp := 2589, conc := 2543, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2590, conc := 2588, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2590, conc := 2589, proof := sorry })
                      (RArray.leaf { hyp := 2591, conc := 2458, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2591, conc := 2502, proof := sorry })
                      (RArray.leaf { hyp := 2591, conc := 2542, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2592, conc := 2503, proof := sorry })
                      (RArray.leaf { hyp := 2592, conc := 2543, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2593, conc := 2543, proof := sorry })
                      (RArray.leaf { hyp := 2594, conc := 2592, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2594, conc := 2593, proof := sorry })
                      (RArray.leaf { hyp := 2595, conc := 2545, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2595, conc := 2591, proof := sorry })
                      (RArray.leaf { hyp := 2597, conc := 2593, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2598, conc := 2593, proof := sorry })
                      (RArray.leaf { hyp := 24, conc := 22, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2599, conc := 2590, proof := sorry })
                      (RArray.leaf { hyp := 2599, conc := 2594, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2599, conc := 2596, proof := sorry })
                      (RArray.leaf { hyp := 2599, conc := 2597, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2599, conc := 2598, proof := sorry })
                      (RArray.leaf { hyp := 2603, conc := 2541, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2603, conc := 2602, proof := sorry })
                      (RArray.leaf { hyp := 2604, conc := 2465, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2604, conc := 2495, proof := sorry })
                      (RArray.leaf { hyp := 2604, conc := 2542, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2605, conc := 2496, proof := sorry })
                      (RArray.leaf { hyp := 2605, conc := 2543, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2606, conc := 2543, proof := sorry })
                      (RArray.leaf { hyp := 2607, conc := 2605, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2607, conc := 2606, proof := sorry })
                      (RArray.leaf { hyp := 2608, conc := 2468, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2608, conc := 2492, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2608, conc := 2542, proof := sorry })
                      (RArray.leaf { hyp := 2609, conc := 2543, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2610, conc := 2543, proof := sorry })
                      (RArray.leaf { hyp := 2611, conc := 2609, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2611, conc := 2610, proof := sorry })
                      (RArray.leaf { hyp := 2612, conc := 2498, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2612, conc := 2545, proof := sorry })
                      (RArray.leaf { hyp := 2612, conc := 2608, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2614, conc := 2610, proof := sorry })
                      (RArray.leaf { hyp := 2615, conc := 2610, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2616, conc := 2607, proof := sorry })
                      (RArray.leaf { hyp := 2616, conc := 2611, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2616, conc := 2613, proof := sorry })
                      (RArray.leaf { hyp := 2616, conc := 2614, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2616, conc := 2615, proof := sorry })
                      (RArray.leaf { hyp := 2617, conc := 2512, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2617, conc := 2549, proof := sorry })
                      (RArray.leaf { hyp := 2617, conc := 2600, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2618, conc := 2567, proof := sorry })
                      (RArray.leaf { hyp := 2618, conc := 2584, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 260, conc := 254, proof := sorry })
                      (RArray.leaf { hyp := 2619, conc := 2550, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2619, conc := 2568, proof := sorry })
                      (RArray.leaf { hyp := 2620, conc := 2514, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2621, conc := 2569, proof := sorry })
                      (RArray.leaf { hyp := 2621, conc := 2586, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2621, conc := 2603, proof := sorry })
                      (RArray.leaf { hyp := 2621, conc := 2619, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2621, conc := 2620, proof := sorry })
                      (RArray.leaf { hyp := 2622, conc := 2516, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2622, conc := 2553, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2622, conc := 2570, proof := sorry })
                      (RArray.leaf { hyp := 2622, conc := 2587, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2626, conc := 2623, proof := sorry })
                      (RArray.leaf { hyp := 2626, conc := 2624, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2626, conc := 2625, proof := sorry })
                      (RArray.leaf { hyp := 2627, conc := 2574, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 261, conc := 255, proof := sorry })
                      (RArray.leaf { hyp := 2629, conc := 2610, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2630, conc := 2610, proof := sorry })
                      (RArray.leaf { hyp := 2631, conc := 2628, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2631, conc := 2629, proof := sorry })
                      (RArray.leaf { hyp := 2631, conc := 2630, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2632, conc := 2520, proof := sorry })
                      (RArray.leaf { hyp := 2634, conc := 2610, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2635, conc := 2610, proof := sorry })
                      (RArray.leaf { hyp := 2636, conc := 2633, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2636, conc := 2634, proof := sorry })
                      (RArray.leaf { hyp := 2636, conc := 2635, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2637, conc := 2561, proof := sorry })
                      (RArray.leaf { hyp := 2637, conc := 2595, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2637, conc := 2612, proof := sorry })
                      (RArray.leaf { hyp := 262, conc := 254, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2640, conc := 2635, proof := sorry })
                      (RArray.leaf { hyp := 2641, conc := 2635, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2642, conc := 2528, proof := sorry })
                      (RArray.leaf { hyp := 2642, conc := 2565, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2642, conc := 2582, proof := sorry })
                      (RArray.leaf { hyp := 2642, conc := 2599, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2642, conc := 2616, proof := sorry })
                      (RArray.leaf { hyp := 2642, conc := 2626, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2642, conc := 2631, proof := sorry })
                      (RArray.leaf { hyp := 2642, conc := 2636, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2642, conc := 2638, proof := sorry })
                      (RArray.leaf { hyp := 2642, conc := 2639, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2642, conc := 2640, proof := sorry })
                      (RArray.leaf { hyp := 2642, conc := 2641, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2645, conc := 2643, proof := sorry })
                      (RArray.leaf { hyp := 2646, conc := 2643, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2647, conc := 2644, proof := sorry })
                      (RArray.leaf { hyp := 2648, conc := 2643, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 263, conc := 254, proof := sorry })
                      (RArray.leaf { hyp := 2649, conc := 2643, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2650, conc := 2644, proof := sorry })
                      (RArray.leaf { hyp := 2651, conc := 2643, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2652, conc := 2643, proof := sorry })
                      (RArray.leaf { hyp := 2653, conc := 2644, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2654, conc := 2645, proof := sorry })
                      (RArray.leaf { hyp := 2654, conc := 2648, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2654, conc := 2651, proof := sorry })
                      (RArray.leaf { hyp := 2655, conc := 2645, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2655, conc := 2649, proof := sorry })
                      (RArray.leaf { hyp := 2655, conc := 2652, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2657, conc := 2656, proof := sorry })
                      (RArray.leaf { hyp := 2658, conc := 2643, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 264, conc := 263, proof := sorry })
                      (RArray.leaf { hyp := 2659, conc := 2643, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2661, conc := 2643, proof := sorry })
                      (RArray.leaf { hyp := 2663, conc := 2644, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2664, conc := 2645, proof := sorry })
                      (RArray.leaf { hyp := 2664, conc := 2658, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2664, conc := 2661, proof := sorry })
                      (RArray.leaf { hyp := 2667, conc := 2666, proof := sorry }))))))))))
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2668, conc := 2643, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2669, conc := 2643, proof := sorry })
                      (RArray.leaf { hyp := 2671, conc := 2643, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2672, conc := 2643, proof := sorry })
                      (RArray.leaf { hyp := 2674, conc := 2645, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2674, conc := 2668, proof := sorry })
                      (RArray.leaf { hyp := 2674, conc := 2671, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2675, conc := 2645, proof := sorry })
                      (RArray.leaf { hyp := 2675, conc := 2669, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2676, conc := 2646, proof := sorry })
                      (RArray.leaf { hyp := 2676, conc := 2668, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2677, conc := 2673, proof := sorry })
                      (RArray.leaf { hyp := 2678, conc := 2648, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2678, conc := 2658, proof := sorry })
                      (RArray.leaf { hyp := 2678, conc := 2668, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2681, conc := 2650, proof := sorry })
                      (RArray.leaf { hyp := 2681, conc := 2670, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2681, conc := 2680, proof := sorry })
                      (RArray.leaf { hyp := 2682, conc := 2648, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2682, conc := 2661, proof := sorry })
                      (RArray.leaf { hyp := 2682, conc := 2671, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2684, conc := 2649, proof := sorry })
                      (RArray.leaf { hyp := 2684, conc := 2661, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2685, conc := 2663, proof := sorry })
                      (RArray.leaf { hyp := 2685, conc := 2683, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2686, conc := 2651, proof := sorry })
                      (RArray.leaf { hyp := 2686, conc := 2658, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2686, conc := 2671, proof := sorry })
                      (RArray.leaf { hyp := 2687, conc := 2651, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2687, conc := 2659, proof := sorry })
                      (RArray.leaf { hyp := 2689, conc := 2653, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2689, conc := 2660, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2690, conc := 2664, proof := sorry })
                      (RArray.leaf { hyp := 2690, conc := 2674, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2690, conc := 2678, proof := sorry })
                      (RArray.leaf { hyp := 2690, conc := 2682, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2690, conc := 2686, proof := sorry })
                      (RArray.leaf { hyp := 2691, conc := 2665, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2691, conc := 2679, proof := sorry })
                      (RArray.leaf { hyp := 2692, conc := 2688, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2693, conc := 2656, proof := sorry })
                      (RArray.leaf { hyp := 2694, conc := 2657, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2694, conc := 2667, proof := sorry })
                      (RArray.leaf { hyp := 2694, conc := 2685, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2694, conc := 2693, proof := sorry })
                      (RArray.leaf { hyp := 2695, conc := 2643, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2696, conc := 2643, proof := sorry })
                      (RArray.leaf { hyp := 2698, conc := 2643, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 268, conc := 258, proof := sorry })
                      (RArray.leaf { hyp := 268, conc := 264, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 25, conc := 22, proof := sorry })
                      (RArray.leaf { hyp := 2699, conc := 2643, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2701, conc := 2645, proof := sorry })
                      (RArray.leaf { hyp := 2701, conc := 2695, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2701, conc := 2698, proof := sorry })
                      (RArray.leaf { hyp := 2704, conc := 2697, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2704, conc := 2702, proof := sorry })
                      (RArray.leaf { hyp := 2705, conc := 2643, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2708, conc := 2643, proof := sorry })
                      (RArray.leaf { hyp := 269, conc := 254, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2709, conc := 2643, proof := sorry })
                      (RArray.leaf { hyp := 2711, conc := 2645, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2711, conc := 2705, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2711, conc := 2708, proof := sorry })
                      (RArray.leaf { hyp := 2714, conc := 2707, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2714, conc := 2710, proof := sorry })
                      (RArray.leaf { hyp := 2715, conc := 2648, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2718, conc := 2717, proof := sorry })
                      (RArray.leaf { hyp := 270, conc := 254, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2721, conc := 2649, proof := sorry })
                      (RArray.leaf { hyp := 2721, conc := 2709, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2722, conc := 2710, proof := sorry })
                      (RArray.leaf { hyp := 2723, conc := 2695, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2723, conc := 2708, proof := sorry })
                      (RArray.leaf { hyp := 2725, conc := 2652, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2726, conc := 2725, proof := sorry })
                      (RArray.leaf { hyp := 2727, conc := 2719, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2728, conc := 2702, proof := sorry })
                      (RArray.leaf { hyp := 2728, conc := 2720, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2729, conc := 2725, proof := sorry })
                      (RArray.leaf { hyp := 2730, conc := 2725, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2731, conc := 2704, proof := sorry })
                      (RArray.leaf { hyp := 2731, conc := 2714, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2731, conc := 2718, proof := sorry })
                      (RArray.leaf { hyp := 2731, conc := 2722, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2731, conc := 2726, proof := sorry })
                      (RArray.leaf { hyp := 2731, conc := 2729, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2731, conc := 2730, proof := sorry })
                      (RArray.leaf { hyp := 2732, conc := 2643, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2733, conc := 2643, proof := sorry })
                      (RArray.leaf { hyp := 2735, conc := 2643, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2736, conc := 2643, proof := sorry })
                      (RArray.leaf { hyp := 2738, conc := 2645, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2738, conc := 2732, proof := sorry })
                      (RArray.leaf { hyp := 2738, conc := 2735, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 272, conc := 254, proof := sorry })
                      (RArray.leaf { hyp := 2740, conc := 2646, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2740, conc := 2736, proof := sorry })
                      (RArray.leaf { hyp := 2741, conc := 2737, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2741, conc := 2739, proof := sorry })
                      (RArray.leaf { hyp := 2742, conc := 2643, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2743, conc := 2643, proof := sorry })
                      (RArray.leaf { hyp := 2745, conc := 2643, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2747, conc := 2746, proof := sorry })
                      (RArray.leaf { hyp := 273, conc := 254, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2749, conc := 2746, proof := sorry })
                      (RArray.leaf { hyp := 2750, conc := 2746, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2751, conc := 2749, proof := sorry })
                      (RArray.leaf { hyp := 2751, conc := 2750, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2754, conc := 2649, proof := sorry })
                      (RArray.leaf { hyp := 2754, conc := 2743, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2755, conc := 2744, proof := sorry })
                      (RArray.leaf { hyp := 2755, conc := 2753, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2758, conc := 2746, proof := sorry })
                      (RArray.leaf { hyp := 2759, conc := 2747, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2759, conc := 2757, proof := sorry })
                      (RArray.leaf { hyp := 2759, conc := 2758, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2760, conc := 2651, proof := sorry })
                      (RArray.leaf { hyp := 2760, conc := 2732, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2762, conc := 2746, proof := sorry })
                      (RArray.leaf { hyp := 2763, conc := 2761, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2764, conc := 2748, proof := sorry })
                      (RArray.leaf { hyp := 2764, conc := 2756, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2765, conc := 2761, proof := sorry })
                      (RArray.leaf { hyp := 2766, conc := 2758, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2768, conc := 2763, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2768, conc := 2765, proof := sorry })
                      (RArray.leaf { hyp := 2768, conc := 2766, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2768, conc := 2767, proof := sorry })
                      (RArray.leaf { hyp := 275, conc := 269, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2769, conc := 2658, proof := sorry })
                      (RArray.leaf { hyp := 2769, conc := 2695, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2769, conc := 2732, proof := sorry })
                      (RArray.leaf { hyp := 2772, conc := 2734, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2773, conc := 2658, proof := sorry })
                      (RArray.leaf { hyp := 2773, conc := 2698, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2773, conc := 2735, proof := sorry })
                      (RArray.leaf { hyp := 2775, conc := 2659, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2775, conc := 2698, proof := sorry })
                      (RArray.leaf { hyp := 2775, conc := 2736, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2776, conc := 2737, proof := sorry })
                      (RArray.leaf { hyp := 2777, conc := 2661, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2777, conc := 2695, proof := sorry })
                      (RArray.leaf { hyp := 2777, conc := 2735, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2780, conc := 2737, proof := sorry })
                      (RArray.leaf { hyp := 2781, conc := 2664, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2781, conc := 2701, proof := sorry })
                      (RArray.leaf { hyp := 2781, conc := 2738, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2781, conc := 2773, proof := sorry })
                      (RArray.leaf { hyp := 2781, conc := 2777, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2782, conc := 2702, proof := sorry })
                      (RArray.leaf { hyp := 2783, conc := 2771, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2784, conc := 2774, proof := sorry })
                      (RArray.leaf { hyp := 2784, conc := 2779, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2785, conc := 2741, proof := sorry })
                      (RArray.leaf { hyp := 2785, conc := 2776, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2785, conc := 2780, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2785, conc := 2782, proof := sorry })
                      (RArray.leaf { hyp := 2785, conc := 2783, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 277, conc := 257, proof := sorry })
                      (RArray.leaf { hyp := 277, conc := 269, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2789, conc := 2744, proof := sorry })
                      (RArray.leaf { hyp := 2791, conc := 2746, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2792, conc := 2746, proof := sorry })
                      (RArray.leaf { hyp := 2793, conc := 2792, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2794, conc := 2661, proof := sorry })
                      (RArray.leaf { hyp := 2794, conc := 2705, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2794, conc := 2745, proof := sorry })
                      (RArray.leaf { hyp := 2795, conc := 2706, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2795, conc := 2746, proof := sorry })
                      (RArray.leaf { hyp := 2796, conc := 2746, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2797, conc := 2795, proof := sorry })
                      (RArray.leaf { hyp := 2797, conc := 2796, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2798, conc := 2748, proof := sorry })
                      (RArray.leaf { hyp := 278, conc := 271, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 278, conc := 274, proof := sorry })
                      (RArray.leaf { hyp := 278, conc := 276, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 278, conc := 277, proof := sorry })
                      (RArray.leaf { hyp := 26, conc := 23, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2800, conc := 2796, proof := sorry })
                      (RArray.leaf { hyp := 2801, conc := 2796, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2802, conc := 2793, proof := sorry })
                      (RArray.leaf { hyp := 2802, conc := 2797, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2802, conc := 2799, proof := sorry })
                      (RArray.leaf { hyp := 2802, conc := 2800, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2802, conc := 2801, proof := sorry })
                      (RArray.leaf { hyp := 2803, conc := 2668, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2804, conc := 2668, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2804, conc := 2696, proof := sorry })
                      (RArray.leaf { hyp := 2804, conc := 2743, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2806, conc := 2744, proof := sorry })
                      (RArray.leaf { hyp := 2807, conc := 2668, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2807, conc := 2698, proof := sorry })
                      (RArray.leaf { hyp := 2807, conc := 2745, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2808, conc := 2699, proof := sorry })
                      (RArray.leaf { hyp := 279, conc := 254, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2809, conc := 2746, proof := sorry })
                      (RArray.leaf { hyp := 2810, conc := 2808, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2810, conc := 2809, proof := sorry })
                      (RArray.leaf { hyp := 2811, conc := 2671, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2811, conc := 2695, proof := sorry })
                      (RArray.leaf { hyp := 2811, conc := 2745, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2814, conc := 2812, proof := sorry })
                      (RArray.leaf { hyp := 2815, conc := 2748, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2816, conc := 2812, proof := sorry })
                      (RArray.leaf { hyp := 2817, conc := 2809, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 280, conc := 254, proof := sorry })
                      (RArray.leaf { hyp := 2819, conc := 2816, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2819, conc := 2817, proof := sorry })
                      (RArray.leaf { hyp := 2819, conc := 2818, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2820, conc := 2678, proof := sorry })
                      (RArray.leaf { hyp := 2820, conc := 2715, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2820, conc := 2752, proof := sorry })
                      (RArray.leaf { hyp := 2820, conc := 2786, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2821, conc := 2770, proof := sorry })
                      (RArray.leaf { hyp := 2822, conc := 2805, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2823, conc := 2805, proof := sorry })
                      (RArray.leaf { hyp := 2824, conc := 2755, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2824, conc := 2789, proof := sorry })
                      (RArray.leaf { hyp := 2824, conc := 2806, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2824, conc := 2821, proof := sorry })
                      (RArray.leaf { hyp := 2824, conc := 2822, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2825, conc := 2756, proof := sorry })
                      (RArray.leaf { hyp := 2825, conc := 2807, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2827, conc := 2809, proof := sorry })
                      (RArray.leaf { hyp := 2828, conc := 2809, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2829, conc := 2826, proof := sorry })
                      (RArray.leaf { hyp := 2829, conc := 2827, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2829, conc := 2828, proof := sorry })
                      (RArray.leaf { hyp := 2830, conc := 2756, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2834, conc := 2814, proof := sorry })
                      (RArray.leaf { hyp := 2834, conc := 2831, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2834, conc := 2832, proof := sorry })
                      (RArray.leaf { hyp := 2834, conc := 2833, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2835, conc := 2686, proof := sorry })
                      (RArray.leaf { hyp := 2835, conc := 2723, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2835, conc := 2790, proof := sorry })
                      (RArray.leaf { hyp := 2835, conc := 2811, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2838, conc := 2762, proof := sorry })
                      (RArray.leaf { hyp := 2838, conc := 2791, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2838, conc := 2813, proof := sorry })
                      (RArray.leaf { hyp := 282, conc := 254, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2839, conc := 2836, proof := sorry })
                      (RArray.leaf { hyp := 2840, conc := 2764, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2840, conc := 2798, proof := sorry })
                      (RArray.leaf { hyp := 2840, conc := 2815, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2840, conc := 2825, proof := sorry })
                      (RArray.leaf { hyp := 2840, conc := 2830, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2841, conc := 2831, proof := sorry })
                      (RArray.leaf { hyp := 2843, conc := 2828, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2845, conc := 2839, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2845, conc := 2841, proof := sorry })
                      (RArray.leaf { hyp := 2845, conc := 2842, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2845, conc := 2843, proof := sorry })
                      (RArray.leaf { hyp := 2845, conc := 2844, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2848, conc := 2846, proof := sorry })
                      (RArray.leaf { hyp := 2849, conc := 2846, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2850, conc := 2847, proof := sorry })
                      (RArray.leaf { hyp := 2851, conc := 2846, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2852, conc := 2846, proof := sorry })
                      (RArray.leaf { hyp := 2853, conc := 2847, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2854, conc := 2846, proof := sorry })
                      (RArray.leaf { hyp := 2855, conc := 2846, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2856, conc := 2847, proof := sorry })
                      (RArray.leaf { hyp := 2859, conc := 2851, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2859, conc := 2855, proof := sorry })
                      (RArray.leaf { hyp := 2860, conc := 2850, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2860, conc := 2856, proof := sorry })
                      (RArray.leaf { hyp := 2861, conc := 2846, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2862, conc := 2846, proof := sorry })
                      (RArray.leaf { hyp := 2864, conc := 2846, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2865, conc := 2846, proof := sorry })
                      (RArray.leaf { hyp := 2867, conc := 2861, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2867, conc := 2864, proof := sorry })
                      (RArray.leaf { hyp := 2870, conc := 2866, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2870, conc := 2868, proof := sorry })
                      (RArray.leaf { hyp := 2871, conc := 2846, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2872, conc := 2846, proof := sorry })
                      (RArray.leaf { hyp := 2873, conc := 2847, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2874, conc := 2846, proof := sorry })
                      (RArray.leaf { hyp := 2875, conc := 2846, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2877, conc := 2848, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2877, conc := 2871, proof := sorry })
                      (RArray.leaf { hyp := 2877, conc := 2874, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2879, conc := 2849, proof := sorry })
                      (RArray.leaf { hyp := 2879, conc := 2871, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2879, conc := 2875, proof := sorry })
                      (RArray.leaf { hyp := 2880, conc := 2873, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2880, conc := 2876, proof := sorry })
                      (RArray.leaf { hyp := 2880, conc := 2878, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2881, conc := 2851, proof := sorry })
                      (RArray.leaf { hyp := 2881, conc := 2861, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2881, conc := 2871, proof := sorry })
                      (RArray.leaf { hyp := 2882, conc := 2851, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2882, conc := 2862, proof := sorry })
                      (RArray.leaf { hyp := 2882, conc := 2872, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2884, conc := 2863, proof := sorry })
                      (RArray.leaf { hyp := 2884, conc := 2873, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2885, conc := 2851, proof := sorry })
                      (RArray.leaf { hyp := 2885, conc := 2864, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2885, conc := 2874, proof := sorry })
                      (RArray.leaf { hyp := 2886, conc := 2851, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2886, conc := 2865, proof := sorry })
                      (RArray.leaf { hyp := 2887, conc := 2852, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2887, conc := 2864, proof := sorry })
                      (RArray.leaf { hyp := 2888, conc := 2866, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 287, conc := 283, proof := sorry })
                      (RArray.leaf { hyp := 2889, conc := 2854, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2889, conc := 2861, proof := sorry })
                      (RArray.leaf { hyp := 2889, conc := 2874, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2890, conc := 2854, proof := sorry })
                      (RArray.leaf { hyp := 2890, conc := 2862, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2892, conc := 2876, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2893, conc := 2867, proof := sorry })
                      (RArray.leaf { hyp := 2893, conc := 2877, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2893, conc := 2885, proof := sorry })
                      (RArray.leaf { hyp := 2893, conc := 2889, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2894, conc := 2857, proof := sorry })
                      (RArray.leaf { hyp := 2894, conc := 2868, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2894, conc := 2882, proof := sorry })
                      (RArray.leaf { hyp := 2895, conc := 2858, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2896, conc := 2869, proof := sorry })
                      (RArray.leaf { hyp := 2896, conc := 2891, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2897, conc := 2860, proof := sorry })
                      (RArray.leaf { hyp := 2897, conc := 2870, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2897, conc := 2888, proof := sorry })
                      (RArray.leaf { hyp := 2897, conc := 2892, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2897, conc := 2894, proof := sorry })
                      (RArray.leaf { hyp := 2897, conc := 2896, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2898, conc := 2846, proof := sorry })
                      (RArray.leaf { hyp := 288, conc := 281, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 288, conc := 284, proof := sorry })
                      (RArray.leaf { hyp := 2899, conc := 2846, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2901, conc := 2846, proof := sorry })
                      (RArray.leaf { hyp := 2902, conc := 2846, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2907, conc := 2903, proof := sorry })
                      (RArray.leaf { hyp := 2907, conc := 2904, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2908, conc := 2846, proof := sorry })
                      (RArray.leaf { hyp := 2909, conc := 2846, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2911, conc := 2846, proof := sorry })
                      (RArray.leaf { hyp := 2917, conc := 2910, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2917, conc := 2913, proof := sorry })
                      (RArray.leaf { hyp := 2917, conc := 2915, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2918, conc := 2898, proof := sorry })
                      (RArray.leaf { hyp := 2918, conc := 2908, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2921, conc := 2919, proof := sorry })
                      (RArray.leaf { hyp := 2924, conc := 2852, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2925, conc := 2903, proof := sorry })
                      (RArray.leaf { hyp := 2927, conc := 2854, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2929, conc := 2913, proof := sorry })
                      (RArray.leaf { hyp := 2929, conc := 2928, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2930, conc := 2914, proof := sorry })
                      (RArray.leaf { hyp := 2930, conc := 2926, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2931, conc := 2905, proof := sorry })
                      (RArray.leaf { hyp := 2931, conc := 2919, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2932, conc := 2904, proof := sorry })
                      (RArray.leaf { hyp := 2933, conc := 2923, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2934, conc := 2907, proof := sorry })
                      (RArray.leaf { hyp := 2934, conc := 2925, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2934, conc := 2929, proof := sorry })
                      (RArray.leaf { hyp := 2934, conc := 2932, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2934, conc := 2933, proof := sorry })
                      (RArray.leaf { hyp := 2935, conc := 2846, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2936, conc := 2846, proof := sorry })
                      (RArray.leaf { hyp := 2938, conc := 2846, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 292, conc := 291, proof := sorry })
                      (RArray.leaf { hyp := 2939, conc := 2846, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2943, conc := 2849, proof := sorry })
                      (RArray.leaf { hyp := 2944, conc := 2937, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2944, conc := 2940, proof := sorry })
                      (RArray.leaf { hyp := 2944, conc := 2942, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2945, conc := 2846, proof := sorry })
                      (RArray.leaf { hyp := 2946, conc := 2846, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2948, conc := 2846, proof := sorry })
                      (RArray.leaf { hyp := 293, conc := 272, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2950, conc := 2949, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2952, conc := 2949, proof := sorry })
                      (RArray.leaf { hyp := 2953, conc := 2949, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2954, conc := 2947, proof := sorry })
                      (RArray.leaf { hyp := 2954, conc := 2952, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2954, conc := 2953, proof := sorry })
                      (RArray.leaf { hyp := 2957, conc := 2935, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2958, conc := 2937, proof := sorry })
                      (RArray.leaf { hyp := 2960, conc := 2949, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2961, conc := 2949, proof := sorry })
                      (RArray.leaf { hyp := 2962, conc := 2960, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2962, conc := 2961, proof := sorry })
                      (RArray.leaf { hyp := 2963, conc := 2854, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2963, conc := 2935, proof := sorry })
                      (RArray.leaf { hyp := 2963, conc := 2948, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2964, conc := 2936, proof := sorry })
                      (RArray.leaf { hyp := 2964, conc := 2949, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2965, conc := 2949, proof := sorry })
                      (RArray.leaf { hyp := 2966, conc := 2964, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2966, conc := 2965, proof := sorry })
                      (RArray.leaf { hyp := 2967, conc := 2857, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2967, conc := 2941, proof := sorry })
                      (RArray.leaf { hyp := 2967, conc := 2951, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2971, conc := 2954, proof := sorry })
                      (RArray.leaf { hyp := 2971, conc := 2958, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2971, conc := 2962, proof := sorry })
                      (RArray.leaf { hyp := 2971, conc := 2966, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2971, conc := 2968, proof := sorry })
                      (RArray.leaf { hyp := 2971, conc := 2969, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2971, conc := 2970, proof := sorry })
                      (RArray.leaf { hyp := 2972, conc := 2861, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2972, conc := 2935, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2975, conc := 2937, proof := sorry })
                      (RArray.leaf { hyp := 2978, conc := 2862, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2978, conc := 2901, proof := sorry })
                      (RArray.leaf { hyp := 296, conc := 284, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2979, conc := 2903, proof := sorry })
                      (RArray.leaf { hyp := 2979, conc := 2977, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2980, conc := 2938, proof := sorry })
                      (RArray.leaf { hyp := 2981, conc := 2864, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2981, conc := 2899, proof := sorry })
                      (RArray.leaf { hyp := 2983, conc := 2982, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2984, conc := 2980, proof := sorry })
                      (RArray.leaf { hyp := 2985, conc := 2942, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2986, conc := 2904, proof := sorry })
                      (RArray.leaf { hyp := 2986, conc := 2982, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2987, conc := 2982, proof := sorry })
                      (RArray.leaf { hyp := 2988, conc := 2907, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2988, conc := 2979, proof := sorry })
                      (RArray.leaf { hyp := 2988, conc := 2985, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2988, conc := 2986, proof := sorry })
                      (RArray.leaf { hyp := 2988, conc := 2987, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2989, conc := 2861, proof := sorry })
                      (RArray.leaf { hyp := 2989, conc := 2908, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2991, conc := 2908, proof := sorry })
                      (RArray.leaf { hyp := 2992, conc := 2910, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2993, conc := 2861, proof := sorry })
                      (RArray.leaf { hyp := 2993, conc := 2911, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2993, conc := 2948, proof := sorry })
                      (RArray.leaf { hyp := 2996, conc := 2950, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2996, conc := 2994, proof := sorry })
                      (RArray.leaf { hyp := 2996, conc := 2995, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2997, conc := 2864, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2997, conc := 2908, proof := sorry })
                      (RArray.leaf { hyp := 2998, conc := 2909, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2998, conc := 2949, proof := sorry })
                      (RArray.leaf { hyp := 298, conc := 270, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3000, conc := 2998, proof := sorry })
                      (RArray.leaf { hyp := 3000, conc := 2999, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3001, conc := 2951, proof := sorry })
                      (RArray.leaf { hyp := 3002, conc := 2994, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3004, conc := 2994, proof := sorry })
                      (RArray.leaf { hyp := 3005, conc := 3000, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3005, conc := 3002, proof := sorry })
                      (RArray.leaf { hyp := 3005, conc := 3003, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3005, conc := 3004, proof := sorry })
                      (RArray.leaf { hyp := 3006, conc := 2871, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3006, conc := 2898, proof := sorry })
                      (RArray.leaf { hyp := 3006, conc := 2945, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3007, conc := 2871, proof := sorry })
                      (RArray.leaf { hyp := 3007, conc := 2899, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3009, conc := 3008, proof := sorry })
                      (RArray.leaf { hyp := 3010, conc := 2871, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3010, conc := 2901, proof := sorry })
                      (RArray.leaf { hyp := 3010, conc := 2948, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3011, conc := 2902, proof := sorry })
                      (RArray.leaf { hyp := 3013, conc := 3011, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3013, conc := 3012, proof := sorry })
                      (RArray.leaf { hyp := 3017, conc := 3015, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3017, conc := 3016, proof := sorry })
                      (RArray.leaf { hyp := 3018, conc := 2951, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3018, conc := 3014, proof := sorry })
                      (RArray.leaf { hyp := 300, conc := 284, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3019, conc := 3011, proof := sorry })
                      (RArray.leaf { hyp := 3021, conc := 3011, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3022, conc := 3013, proof := sorry })
                      (RArray.leaf { hyp := 3022, conc := 3017, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3022, conc := 3019, proof := sorry })
                      (RArray.leaf { hyp := 3022, conc := 3020, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3022, conc := 3021, proof := sorry })
                      (RArray.leaf { hyp := 3023, conc := 2918, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3023, conc := 2955, proof := sorry })
                      (RArray.leaf { hyp := 3023, conc := 2972, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3023, conc := 2989, proof := sorry })
                      (RArray.leaf { hyp := 3024, conc := 2919, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3025, conc := 2956, proof := sorry })
                      (RArray.leaf { hyp := 3025, conc := 2974, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3027, conc := 2992, proof := sorry })
                      (RArray.leaf { hyp := 3027, conc := 3009, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3027, conc := 3024, proof := sorry })
                      (RArray.leaf { hyp := 3028, conc := 2959, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3028, conc := 2976, proof := sorry })
                      (RArray.leaf { hyp := 301, conc := 275, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 301, conc := 285, proof := sorry })
                      (RArray.leaf { hyp := 301, conc := 293, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 301, conc := 297, proof := sorry })
                      (RArray.leaf { hyp := 3029, conc := 3011, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3032, conc := 3029, proof := sorry })
                      (RArray.leaf { hyp := 3032, conc := 3030, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3032, conc := 3031, proof := sorry })
                      (RArray.leaf { hyp := 3033, conc := 2980, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3033, conc := 2997, proof := sorry })
                      (RArray.leaf { hyp := 3037, conc := 3034, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3037, conc := 3035, proof := sorry })
                      (RArray.leaf { hyp := 3037, conc := 3036, proof := sorry })))))))))))
  (RArray.branch 500
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3038, conc := 2926, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3038, conc := 2963, proof := sorry })
                      (RArray.leaf { hyp := 3038, conc := 2993, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3040, conc := 3016, proof := sorry })
                      (RArray.leaf { hyp := 3041, conc := 3016, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3042, conc := 3039, proof := sorry })
                      (RArray.leaf { hyp := 3042, conc := 3040, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3042, conc := 3041, proof := sorry })
                      (RArray.leaf { hyp := 3043, conc := 2930, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3043, conc := 2967, proof := sorry })
                      (RArray.leaf { hyp := 3043, conc := 2984, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3043, conc := 3001, proof := sorry })
                      (RArray.leaf { hyp := 3043, conc := 3018, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3043, conc := 3033, proof := sorry })
                      (RArray.leaf { hyp := 3043, conc := 3038, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3044, conc := 3039, proof := sorry })
                      (RArray.leaf { hyp := 3048, conc := 2934, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3048, conc := 2988, proof := sorry })
                      (RArray.leaf { hyp := 3048, conc := 3005, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3048, conc := 3022, proof := sorry })
                      (RArray.leaf { hyp := 3048, conc := 3032, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3048, conc := 3037, proof := sorry })
                      (RArray.leaf { hyp := 3048, conc := 3042, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3048, conc := 3044, proof := sorry })
                      (RArray.leaf { hyp := 3048, conc := 3045, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3048, conc := 3046, proof := sorry })
                      (RArray.leaf { hyp := 3048, conc := 3047, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 303, conc := 291, proof := sorry })
                      (RArray.leaf { hyp := 3051, conc := 3049, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3052, conc := 3049, proof := sorry })
                      (RArray.leaf { hyp := 3053, conc := 3050, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3054, conc := 3049, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3055, conc := 3049, proof := sorry })
                      (RArray.leaf { hyp := 3057, conc := 3049, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 304, conc := 287, proof := sorry })
                      (RArray.leaf { hyp := 304, conc := 294, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 304, conc := 299, proof := sorry })
                      (RArray.leaf { hyp := 3059, conc := 3050, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3063, conc := 3053, proof := sorry })
                      (RArray.leaf { hyp := 3063, conc := 3056, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3063, conc := 3060, proof := sorry })
                      (RArray.leaf { hyp := 3063, conc := 3061, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3064, conc := 3049, proof := sorry })
                      (RArray.leaf { hyp := 3065, conc := 3049, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3066, conc := 3050, proof := sorry })
                      (RArray.leaf { hyp := 3067, conc := 3049, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3068, conc := 3049, proof := sorry })
                      (RArray.leaf { hyp := 305, conc := 278, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3070, conc := 3051, proof := sorry })
                      (RArray.leaf { hyp := 3070, conc := 3064, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3070, conc := 3067, proof := sorry })
                      (RArray.leaf { hyp := 3072, conc := 3052, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3072, conc := 3068, proof := sorry })
                      (RArray.leaf { hyp := 3073, conc := 3066, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3073, conc := 3069, proof := sorry })
                      (RArray.leaf { hyp := 3073, conc := 3072, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3074, conc := 3049, proof := sorry })
                      (RArray.leaf { hyp := 3075, conc := 3049, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3077, conc := 3049, proof := sorry })
                      (RArray.leaf { hyp := 3078, conc := 3049, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3079, conc := 3050, proof := sorry })
                      (RArray.leaf { hyp := 3082, conc := 3052, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3082, conc := 3074, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3082, conc := 3078, proof := sorry })
                      (RArray.leaf { hyp := 3083, conc := 3076, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3084, conc := 3054, proof := sorry })
                      (RArray.leaf { hyp := 3084, conc := 3064, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3084, conc := 3074, proof := sorry })
                      (RArray.leaf { hyp := 3085, conc := 3075, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3087, conc := 3056, proof := sorry })
                      (RArray.leaf { hyp := 3087, conc := 3086, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3088, conc := 3054, proof := sorry })
                      (RArray.leaf { hyp := 3088, conc := 3077, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 307, conc := 306, proof := sorry })
                      (RArray.leaf { hyp := 3089, conc := 3068, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3090, conc := 3055, proof := sorry })
                      (RArray.leaf { hyp := 3090, conc := 3067, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3090, conc := 3078, proof := sorry })
                      (RArray.leaf { hyp := 3091, conc := 3089, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3092, conc := 3057, proof := sorry })
                      (RArray.leaf { hyp := 3092, conc := 3077, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3093, conc := 3057, proof := sorry })
                      (RArray.leaf { hyp := 3093, conc := 3065, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3094, conc := 3058, proof := sorry })
                      (RArray.leaf { hyp := 3095, conc := 3094, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3096, conc := 3080, proof := sorry })
                      (RArray.leaf { hyp := 3096, conc := 3084, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3096, conc := 3088, proof := sorry })
                      (RArray.leaf { hyp := 3096, conc := 3092, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3097, conc := 3085, proof := sorry })
                      (RArray.leaf { hyp := 3097, conc := 3089, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3098, conc := 3061, proof := sorry })
                      (RArray.leaf { hyp := 3098, conc := 3090, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 308, conc := 306, proof := sorry })
                      (RArray.leaf { hyp := 3099, conc := 3062, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3099, conc := 3082, proof := sorry })
                      (RArray.leaf { hyp := 3100, conc := 3063, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3100, conc := 3087, proof := sorry })
                      (RArray.leaf { hyp := 3100, conc := 3091, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3100, conc := 3095, proof := sorry })
                      (RArray.leaf { hyp := 3100, conc := 3098, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3100, conc := 3099, proof := sorry })
                      (RArray.leaf { hyp := 3102, conc := 3049, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3104, conc := 3049, proof := sorry })
                      (RArray.leaf { hyp := 3105, conc := 3049, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3107, conc := 3104, proof := sorry })
                      (RArray.leaf { hyp := 309, conc := 306, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3110, conc := 3103, proof := sorry })
                      (RArray.leaf { hyp := 3110, conc := 3106, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3110, conc := 3109, proof := sorry })
                      (RArray.leaf { hyp := 3111, conc := 3049, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3114, conc := 3049, proof := sorry })
                      (RArray.leaf { hyp := 3115, conc := 3049, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 310, conc := 307, proof := sorry })
                      (RArray.leaf { hyp := 310, conc := 308, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3120, conc := 3116, proof := sorry })
                      (RArray.leaf { hyp := 3121, conc := 3054, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3121, conc := 3101, proof := sorry })
                      (RArray.leaf { hyp := 3121, conc := 3111, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3124, conc := 3103, proof := sorry })
                      (RArray.leaf { hyp := 3124, conc := 3123, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3127, conc := 3104, proof := sorry })
                      (RArray.leaf { hyp := 3128, conc := 3106, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 311, conc := 306, proof := sorry })
                      (RArray.leaf { hyp := 3130, conc := 3102, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3132, conc := 3116, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3133, conc := 3117, proof := sorry })
                      (RArray.leaf { hyp := 3133, conc := 3125, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3135, conc := 3118, proof := sorry })
                      (RArray.leaf { hyp := 3135, conc := 3123, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3135, conc := 3131, proof := sorry })
                      (RArray.leaf { hyp := 3136, conc := 3109, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3137, conc := 3124, proof := sorry })
                      (RArray.leaf { hyp := 3137, conc := 3128, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3137, conc := 3132, proof := sorry })
                      (RArray.leaf { hyp := 3137, conc := 3136, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3138, conc := 3049, proof := sorry })
                      (RArray.leaf { hyp := 312, conc := 306, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3139, conc := 3049, proof := sorry })
                      (RArray.leaf { hyp := 3142, conc := 3049, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3144, conc := 3141, proof := sorry })
                      (RArray.leaf { hyp := 3147, conc := 3145, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3148, conc := 3049, proof := sorry })
                      (RArray.leaf { hyp := 3149, conc := 3049, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3151, conc := 3049, proof := sorry })
                      (RArray.leaf { hyp := 3157, conc := 3150, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3157, conc := 3153, proof := sorry })
                      (RArray.leaf { hyp := 3157, conc := 3155, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3157, conc := 3156, proof := sorry })
                      (RArray.leaf { hyp := 314, conc := 306, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3160, conc := 3055, proof := sorry })
                      (RArray.leaf { hyp := 3160, conc := 3138, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3160, conc := 3149, proof := sorry })
                      (RArray.leaf { hyp := 3161, conc := 3158, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3165, conc := 3163, proof := sorry })
                      (RArray.leaf { hyp := 3166, conc := 3057, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3166, conc := 3138, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3166, conc := 3151, proof := sorry })
                      (RArray.leaf { hyp := 3167, conc := 3139, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3169, conc := 3140, proof := sorry })
                      (RArray.leaf { hyp := 3169, conc := 3167, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3169, conc := 3168, proof := sorry })
                      (RArray.leaf { hyp := 3170, conc := 3154, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3171, conc := 3159, proof := sorry })
                      (RArray.leaf { hyp := 3174, conc := 3161, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3174, conc := 3165, proof := sorry })
                      (RArray.leaf { hyp := 3174, conc := 3169, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3174, conc := 3171, proof := sorry })
                      (RArray.leaf { hyp := 3174, conc := 3172, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3174, conc := 3173, proof := sorry })
                      (RArray.leaf { hyp := 3175, conc := 3064, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3175, conc := 3101, proof := sorry })
                      (RArray.leaf { hyp := 3175, conc := 3138, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3178, conc := 3103, proof := sorry })
                      (RArray.leaf { hyp := 3178, conc := 3140, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3178, conc := 3177, proof := sorry })
                      (RArray.leaf { hyp := 316, conc := 307, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 316, conc := 314, proof := sorry })
                      (RArray.leaf { hyp := 3179, conc := 3104, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3182, conc := 3143, proof := sorry })
                      (RArray.leaf { hyp := 3184, conc := 3102, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3186, conc := 3103, proof := sorry })
                      (RArray.leaf { hyp := 3187, conc := 3183, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3188, conc := 3145, proof := sorry })
                      (RArray.leaf { hyp := 317, conc := 308, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 317, conc := 314, proof := sorry })
                      (RArray.leaf { hyp := 3189, conc := 3185, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3190, conc := 3072, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3190, conc := 3109, proof := sorry })
                      (RArray.leaf { hyp := 3190, conc := 3175, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3191, conc := 3186, proof := sorry })
                      (RArray.leaf { hyp := 3191, conc := 3188, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3191, conc := 3190, proof := sorry })
                      (RArray.leaf { hyp := 3194, conc := 3065, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3194, conc := 3111, proof := sorry })
                      (RArray.leaf { hyp := 3195, conc := 3193, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3196, conc := 3064, proof := sorry })
                      (RArray.leaf { hyp := 3196, conc := 3114, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3196, conc := 3151, proof := sorry })
                      (RArray.leaf { hyp := 3198, conc := 3152, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 318, conc := 308, proof := sorry })
                      (RArray.leaf { hyp := 318, conc := 312, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3199, conc := 3197, proof := sorry })
                      (RArray.leaf { hyp := 3200, conc := 3067, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3200, conc := 3111, proof := sorry })
                      (RArray.leaf { hyp := 3200, conc := 3151, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3201, conc := 3112, proof := sorry })
                      (RArray.leaf { hyp := 3203, conc := 3202, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3204, conc := 3154, proof := sorry })
                      (RArray.leaf { hyp := 3205, conc := 3197, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3207, conc := 3197, proof := sorry })
                      (RArray.leaf { hyp := 3208, conc := 3203, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3208, conc := 3205, proof := sorry })
                      (RArray.leaf { hyp := 3208, conc := 3206, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3208, conc := 3207, proof := sorry })
                      (RArray.leaf { hyp := 319, conc := 309, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 319, conc := 315, proof := sorry })
                      (RArray.leaf { hyp := 3209, conc := 3148, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3212, conc := 3103, proof := sorry })
                      (RArray.leaf { hyp := 3213, conc := 3074, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3213, conc := 3104, proof := sorry })
                      (RArray.leaf { hyp := 3214, conc := 3105, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3215, conc := 3152, proof := sorry })
                      (RArray.leaf { hyp := 3216, conc := 3214, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3216, conc := 3215, proof := sorry })
                      (RArray.leaf { hyp := 320, conc := 313, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 320, conc := 318, proof := sorry })
                      (RArray.leaf { hyp := 3220, conc := 3218, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3221, conc := 3080, proof := sorry })
                      (RArray.leaf { hyp := 3221, conc := 3154, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3222, conc := 3214, proof := sorry })
                      (RArray.leaf { hyp := 3224, conc := 3214, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3225, conc := 3212, proof := sorry })
                      (RArray.leaf { hyp := 3225, conc := 3220, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3225, conc := 3222, proof := sorry })
                      (RArray.leaf { hyp := 3225, conc := 3223, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3225, conc := 3224, proof := sorry })
                      (RArray.leaf { hyp := 3226, conc := 3084, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3226, conc := 3121, proof := sorry })
                      (RArray.leaf { hyp := 3226, conc := 3192, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3226, conc := 3209, proof := sorry })
                      (RArray.leaf { hyp := 3227, conc := 3122, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3227, conc := 3159, proof := sorry })
                      (RArray.leaf { hyp := 3228, conc := 3159, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3229, conc := 3123, proof := sorry })
                      (RArray.leaf { hyp := 3229, conc := 3193, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3229, conc := 3211, proof := sorry })
                      (RArray.leaf { hyp := 3230, conc := 3124, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3230, conc := 3212, proof := sorry })
                      (RArray.leaf { hyp := 3230, conc := 3228, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3231, conc := 3125, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3231, conc := 3213, proof := sorry })
                      (RArray.leaf { hyp := 3234, conc := 3215, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3235, conc := 3128, proof := sorry })
                      (RArray.leaf { hyp := 3235, conc := 3182, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3235, conc := 3232, proof := sorry })
                      (RArray.leaf { hyp := 3235, conc := 3233, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3235, conc := 3234, proof := sorry })
                      (RArray.leaf { hyp := 3236, conc := 3162, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3238, conc := 3185, proof := sorry })
                      (RArray.leaf { hyp := 322, conc := 306, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3239, conc := 3164, proof := sorry })
                      (RArray.leaf { hyp := 3239, conc := 3201, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3239, conc := 3219, proof := sorry })
                      (RArray.leaf { hyp := 3240, conc := 3237, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3241, conc := 3129, proof := sorry })
                      (RArray.leaf { hyp := 3241, conc := 3217, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3245, conc := 3242, proof := sorry })
                      (RArray.leaf { hyp := 3246, conc := 3133, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3246, conc := 3170, proof := sorry })
                      (RArray.leaf { hyp := 3246, conc := 3204, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3246, conc := 3221, proof := sorry })
                      (RArray.leaf { hyp := 3246, conc := 3231, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3246, conc := 3236, proof := sorry })
                      (RArray.leaf { hyp := 3247, conc := 3232, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 323, conc := 321, proof := sorry })
                      (RArray.leaf { hyp := 3249, conc := 3187, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3249, conc := 3234, proof := sorry })
                      (RArray.leaf { hyp := 3251, conc := 3245, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3251, conc := 3247, proof := sorry })
                      (RArray.leaf { hyp := 3251, conc := 3248, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3251, conc := 3249, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3251, conc := 3250, proof := sorry })
                      (RArray.leaf { hyp := 3253, conc := 3252, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3254, conc := 3252, proof := sorry })
                      (RArray.leaf { hyp := 3255, conc := 3252, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3256, conc := 3253, proof := sorry })
                      (RArray.leaf { hyp := 3256, conc := 3254, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3256, conc := 3255, proof := sorry })
                      (RArray.leaf { hyp := 3257, conc := 3252, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3258, conc := 3252, proof := sorry })
                      (RArray.leaf { hyp := 324, conc := 306, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3259, conc := 3253, proof := sorry })
                      (RArray.leaf { hyp := 3259, conc := 3258, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3260, conc := 3252, proof := sorry })
                      (RArray.leaf { hyp := 3261, conc := 3252, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3262, conc := 3253, proof := sorry })
                      (RArray.leaf { hyp := 3262, conc := 3260, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3263, conc := 3254, proof := sorry })
                      (RArray.leaf { hyp := 3263, conc := 3257, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3263, conc := 3260, proof := sorry })
                      (RArray.leaf { hyp := 3264, conc := 3254, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3264, conc := 3258, proof := sorry })
                      (RArray.leaf { hyp := 3264, conc := 3261, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3265, conc := 3255, proof := sorry })
                      (RArray.leaf { hyp := 3265, conc := 3257, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3265, conc := 3261, proof := sorry })
                      (RArray.leaf { hyp := 3266, conc := 3256, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3266, conc := 3259, proof := sorry })
                      (RArray.leaf { hyp := 3266, conc := 3262, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3266, conc := 3263, proof := sorry })
                      (RArray.leaf { hyp := 3266, conc := 3264, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3267, conc := 3252, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3268, conc := 3252, proof := sorry })
                      (RArray.leaf { hyp := 325, conc := 306, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3270, conc := 3252, proof := sorry })
                      (RArray.leaf { hyp := 3271, conc := 3252, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3273, conc := 3254, proof := sorry })
                      (RArray.leaf { hyp := 3273, conc := 3270, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3276, conc := 3269, proof := sorry })
                      (RArray.leaf { hyp := 3276, conc := 3274, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3277, conc := 3252, proof := sorry })
                      (RArray.leaf { hyp := 3278, conc := 3252, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 326, conc := 325, proof := sorry })
                      (RArray.leaf { hyp := 3280, conc := 3252, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3282, conc := 3253, proof := sorry })
                      (RArray.leaf { hyp := 3282, conc := 3280, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3283, conc := 3254, proof := sorry })
                      (RArray.leaf { hyp := 3283, conc := 3280, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3284, conc := 3254, proof := sorry })
                      (RArray.leaf { hyp := 3284, conc := 3278, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3284, conc := 3281, proof := sorry })
                      (RArray.leaf { hyp := 3285, conc := 3255, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3285, conc := 3277, proof := sorry })
                      (RArray.leaf { hyp := 3285, conc := 3281, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3286, conc := 3279, proof := sorry })
                      (RArray.leaf { hyp := 3287, conc := 3257, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3287, conc := 3267, proof := sorry })
                      (RArray.leaf { hyp := 3287, conc := 3277, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 327, conc := 321, proof := sorry })
                      (RArray.leaf { hyp := 3290, conc := 3288, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3291, conc := 3270, proof := sorry })
                      (RArray.leaf { hyp := 3291, conc := 3280, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3292, conc := 3257, proof := sorry })
                      (RArray.leaf { hyp := 3292, conc := 3271, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3292, conc := 3281, proof := sorry })
                      (RArray.leaf { hyp := 3293, conc := 3258, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3293, conc := 3270, proof := sorry })
                      (RArray.leaf { hyp := 3293, conc := 3281, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3294, conc := 3259, proof := sorry })
                      (RArray.leaf { hyp := 3294, conc := 3272, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3294, conc := 3282, proof := sorry })
                      (RArray.leaf { hyp := 3294, conc := 3291, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3294, conc := 3293, proof := sorry })
                      (RArray.leaf { hyp := 3295, conc := 3260, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3295, conc := 3280, proof := sorry })
                      (RArray.leaf { hyp := 3296, conc := 3260, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3296, conc := 3268, proof := sorry })
                      (RArray.leaf { hyp := 3296, conc := 3281, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3298, conc := 3262, proof := sorry })
                      (RArray.leaf { hyp := 3298, conc := 3269, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3298, conc := 3282, proof := sorry })
                      (RArray.leaf { hyp := 3298, conc := 3295, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3298, conc := 3296, proof := sorry })
                      (RArray.leaf { hyp := 328, conc := 308, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 328, conc := 322, proof := sorry })
                      (RArray.leaf { hyp := 328, conc := 325, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3299, conc := 3263, proof := sorry })
                      (RArray.leaf { hyp := 3299, conc := 3273, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3299, conc := 3283, proof := sorry })
                      (RArray.leaf { hyp := 3299, conc := 3291, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3299, conc := 3295, proof := sorry })
                      (RArray.leaf { hyp := 3300, conc := 3263, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3300, conc := 3274, proof := sorry })
                      (RArray.leaf { hyp := 3300, conc := 3284, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3300, conc := 3288, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3300, conc := 3296, proof := sorry })
                      (RArray.leaf { hyp := 3301, conc := 3264, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3301, conc := 3273, proof := sorry })
                      (RArray.leaf { hyp := 3301, conc := 3284, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3301, conc := 3289, proof := sorry })
                      (RArray.leaf { hyp := 3301, conc := 3293, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3302, conc := 3275, proof := sorry })
                      (RArray.leaf { hyp := 3302, conc := 3292, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3303, conc := 3276, proof := sorry })
                      (RArray.leaf { hyp := 3303, conc := 3286, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3303, conc := 3290, proof := sorry })
                      (RArray.leaf { hyp := 3303, conc := 3299, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3303, conc := 3301, proof := sorry })
                      (RArray.leaf { hyp := 3305, conc := 3252, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3306, conc := 3304, proof := sorry })
                      (RArray.leaf { hyp := 3307, conc := 3252, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3308, conc := 3252, proof := sorry })
                      (RArray.leaf { hyp := 329, conc := 321, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3309, conc := 3308, proof := sorry })
                      (RArray.leaf { hyp := 3310, conc := 3304, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3311, conc := 3308, proof := sorry })
                      (RArray.leaf { hyp := 3312, conc := 3304, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3313, conc := 3306, proof := sorry })
                      (RArray.leaf { hyp := 3313, conc := 3310, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3314, conc := 3252, proof := sorry })
                      (RArray.leaf { hyp := 3315, conc := 3252, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3316, conc := 3253, proof := sorry })
                      (RArray.leaf { hyp := 3316, conc := 3314, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3317, conc := 3252, proof := sorry })
                      (RArray.leaf { hyp := 3318, conc := 3252, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 330, conc := 310, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 330, conc := 326, proof := sorry })
                      (RArray.leaf { hyp := 330, conc := 328, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 330, conc := 329, proof := sorry })
                      (RArray.leaf { hyp := 3319, conc := 3253, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3319, conc := 3317, proof := sorry })
                      (RArray.leaf { hyp := 3320, conc := 3254, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3320, conc := 3314, proof := sorry })
                      (RArray.leaf { hyp := 3320, conc := 3317, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3321, conc := 3254, proof := sorry })
                      (RArray.leaf { hyp := 3321, conc := 3315, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3321, conc := 3318, proof := sorry })
                      (RArray.leaf { hyp := 3322, conc := 3255, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3322, conc := 3314, proof := sorry })
                      (RArray.leaf { hyp := 3322, conc := 3318, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3323, conc := 3316, proof := sorry })
                      (RArray.leaf { hyp := 3323, conc := 3319, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3323, conc := 3320, proof := sorry })
                      (RArray.leaf { hyp := 3323, conc := 3321, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3323, conc := 3322, proof := sorry })
                      (RArray.leaf { hyp := 3324, conc := 3304, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3325, conc := 3257, proof := sorry })
                      (RArray.leaf { hyp := 3325, conc := 3305, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3325, conc := 3315, proof := sorry })
                      (RArray.leaf { hyp := 3326, conc := 3304, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3327, conc := 3326, proof := sorry })
                      (RArray.leaf { hyp := 3330, conc := 3258, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3330, conc := 3307, proof := sorry })
                      (RArray.leaf { hyp := 3330, conc := 3318, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3331, conc := 3309, proof := sorry })
                      (RArray.leaf { hyp := 3331, conc := 3328, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3331, conc := 3329, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3332, conc := 3304, proof := sorry })
                      (RArray.leaf { hyp := 3333, conc := 3260, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3333, conc := 3305, proof := sorry })
                      (RArray.leaf { hyp := 3333, conc := 3318, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3334, conc := 3304, proof := sorry })
                      (RArray.leaf { hyp := 3335, conc := 3332, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3336, conc := 3332, proof := sorry })
                      (RArray.leaf { hyp := 3337, conc := 3263, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3337, conc := 3311, proof := sorry })
                      (RArray.leaf { hyp := 3337, conc := 3321, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3337, conc := 3325, proof := sorry })
                      (RArray.leaf { hyp := 3337, conc := 3329, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3337, conc := 3333, proof := sorry })
                      (RArray.leaf { hyp := 3338, conc := 3326, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3338, conc := 3330, proof := sorry })
                      (RArray.leaf { hyp := 332, conc := 306, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3339, conc := 3312, proof := sorry })
                      (RArray.leaf { hyp := 3339, conc := 3324, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3339, conc := 3334, proof := sorry })
                      (RArray.leaf { hyp := 3340, conc := 3266, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3340, conc := 3313, proof := sorry })
                      (RArray.leaf { hyp := 3340, conc := 3335, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3340, conc := 3336, proof := sorry })
                      (RArray.leaf { hyp := 3341, conc := 3252, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3342, conc := 3252, proof := sorry })
                      (RArray.leaf { hyp := 3344, conc := 3252, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3345, conc := 3252, proof := sorry })
                      (RArray.leaf { hyp := 3349, conc := 3341, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3349, conc := 3345, proof := sorry })
                      (RArray.leaf { hyp := 3350, conc := 3343, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3350, conc := 3347, proof := sorry })
                      (RArray.leaf { hyp := 3350, conc := 3348, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3350, conc := 3349, proof := sorry })
                      (RArray.leaf { hyp := 3351, conc := 3252, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3352, conc := 3252, proof := sorry })
                      (RArray.leaf { hyp := 3354, conc := 3252, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3358, conc := 3355, proof := sorry })
                      (RArray.leaf { hyp := 334, conc := 306, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3360, conc := 3256, proof := sorry })
                      (RArray.leaf { hyp := 3360, conc := 3353, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3360, conc := 3356, proof := sorry })
                      (RArray.leaf { hyp := 3360, conc := 3359, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3363, conc := 3341, proof := sorry })
                      (RArray.leaf { hyp := 3363, conc := 3352, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3364, conc := 3343, proof := sorry })
                      (RArray.leaf { hyp := 3364, conc := 3353, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3364, conc := 3361, proof := sorry })
                      (RArray.leaf { hyp := 3368, conc := 3365, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3368, conc := 3367, proof := sorry })
                      (RArray.leaf { hyp := 3369, conc := 3354, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3372, conc := 3371, proof := sorry })
                      (RArray.leaf { hyp := 3373, conc := 3361, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3374, conc := 3358, proof := sorry })
                      (RArray.leaf { hyp := 3374, conc := 3370, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3375, conc := 3367, proof := sorry })
                      (RArray.leaf { hyp := 3376, conc := 3361, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3376, conc := 3371, proof := sorry })
                      (RArray.leaf { hyp := 3377, conc := 3364, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3377, conc := 3373, proof := sorry })
                      (RArray.leaf { hyp := 3377, conc := 3375, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 336, conc := 334, proof := sorry })
                      (RArray.leaf { hyp := 3379, conc := 3342, proof := sorry }))))))))))
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3380, conc := 3268, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3381, conc := 3269, proof := sorry })
                      (RArray.leaf { hyp := 3381, conc := 3380, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3385, conc := 3309, proof := sorry })
                      (RArray.leaf { hyp := 3385, conc := 3382, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3385, conc := 3383, proof := sorry })
                      (RArray.leaf { hyp := 3386, conc := 3344, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3387, conc := 3270, proof := sorry })
                      (RArray.leaf { hyp := 3387, conc := 3345, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 337, conc := 331, proof := sorry })
                      (RArray.leaf { hyp := 3389, conc := 3272, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3389, conc := 3386, proof := sorry })
                      (RArray.leaf { hyp := 3391, conc := 3311, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3391, conc := 3348, proof := sorry })
                      (RArray.leaf { hyp := 3391, conc := 3379, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3391, conc := 3387, proof := sorry })
                      (RArray.leaf { hyp := 3393, conc := 3388, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3394, conc := 3381, proof := sorry })
                      (RArray.leaf { hyp := 3394, conc := 3385, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3394, conc := 3389, proof := sorry })
                      (RArray.leaf { hyp := 3394, conc := 3390, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3394, conc := 3391, proof := sorry })
                      (RArray.leaf { hyp := 3394, conc := 3392, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3398, conc := 3395, proof := sorry })
                      (RArray.leaf { hyp := 32, conc := 31, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3400, conc := 3267, proof := sorry })
                      (RArray.leaf { hyp := 3400, conc := 3355, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3402, conc := 3319, proof := sorry })
                      (RArray.leaf { hyp := 3402, conc := 3401, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3404, conc := 3315, proof := sorry })
                      (RArray.leaf { hyp := 3404, conc := 3355, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3406, conc := 3405, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3408, conc := 3404, proof := sorry })
                      (RArray.leaf { hyp := 3409, conc := 3401, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3411, conc := 3398, proof := sorry })
                      (RArray.leaf { hyp := 3411, conc := 3402, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3411, conc := 3406, proof := sorry })
                      (RArray.leaf { hyp := 3411, conc := 3407, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3411, conc := 3409, proof := sorry })
                      (RArray.leaf { hyp := 3412, conc := 3351, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3413, conc := 3277, proof := sorry })
                      (RArray.leaf { hyp := 3413, conc := 3305, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3413, conc := 3352, proof := sorry })
                      (RArray.leaf { hyp := 3415, conc := 3414, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 340, conc := 336, proof := sorry })
                      (RArray.leaf { hyp := 340, conc := 337, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3419, conc := 3418, proof := sorry })
                      (RArray.leaf { hyp := 3422, conc := 3281, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3423, conc := 3420, proof := sorry })
                      (RArray.leaf { hyp := 3425, conc := 3358, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3426, conc := 3414, proof := sorry })
                      (RArray.leaf { hyp := 3427, conc := 3422, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3428, conc := 3415, proof := sorry })
                      (RArray.leaf { hyp := 3428, conc := 3424, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3429, conc := 3412, proof := sorry })
                      (RArray.leaf { hyp := 3430, conc := 3287, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3430, conc := 3325, proof := sorry })
                      (RArray.leaf { hyp := 3430, conc := 3362, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3430, conc := 3379, proof := sorry })
                      (RArray.leaf { hyp := 3430, conc := 3413, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3432, conc := 3414, proof := sorry })
                      (RArray.leaf { hyp := 3433, conc := 3290, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3433, conc := 3364, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3434, conc := 3382, proof := sorry })
                      (RArray.leaf { hyp := 3435, conc := 3329, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3435, conc := 3400, proof := sorry })
                      (RArray.leaf { hyp := 3435, conc := 3417, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3436, conc := 3401, proof := sorry })
                      (RArray.leaf { hyp := 3437, conc := 3382, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3437, conc := 3418, proof := sorry })
                      (RArray.leaf { hyp := 3438, conc := 3368, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3438, conc := 3385, proof := sorry })
                      (RArray.leaf { hyp := 3438, conc := 3419, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3438, conc := 3434, proof := sorry })
                      (RArray.leaf { hyp := 3438, conc := 3436, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 342, conc := 311, proof := sorry })
                      (RArray.leaf { hyp := 342, conc := 322, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 342, conc := 332, proof := sorry })
                      (RArray.leaf { hyp := 3440, conc := 3404, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3440, conc := 3421, proof := sorry })
                      (RArray.leaf { hyp := 3441, conc := 3422, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3442, conc := 3367, proof := sorry })
                      (RArray.leaf { hyp := 3443, conc := 3439, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3443, conc := 3442, proof := sorry })
                      (RArray.leaf { hyp := 3445, conc := 3370, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3445, conc := 3421, proof := sorry })
                      (RArray.leaf { hyp := 3446, conc := 3401, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3447, conc := 3371, proof := sorry })
                      (RArray.leaf { hyp := 3447, conc := 3378, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3447, conc := 3422, proof := sorry })
                      (RArray.leaf { hyp := 3448, conc := 3423, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3448, conc := 3444, proof := sorry })
                      (RArray.leaf { hyp := 3448, conc := 3446, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3449, conc := 3407, proof := sorry })
                      (RArray.leaf { hyp := 3450, conc := 3337, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3450, conc := 3374, proof := sorry })
                      (RArray.leaf { hyp := 3450, conc := 3391, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3451, conc := 3431, proof := sorry })
                      (RArray.leaf { hyp := 3451, conc := 3446, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3452, conc := 3426, proof := sorry })
                      (RArray.leaf { hyp := 3452, conc := 3432, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3453, conc := 3393, proof := sorry })
                      (RArray.leaf { hyp := 3453, conc := 3410, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3454, conc := 3303, proof := sorry })
                      (RArray.leaf { hyp := 3454, conc := 3428, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3454, conc := 3433, proof := sorry })
                      (RArray.leaf { hyp := 3454, conc := 3449, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3456, conc := 3455, proof := sorry })
                      (RArray.leaf { hyp := 3457, conc := 3455, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3458, conc := 3455, proof := sorry })
                      (RArray.leaf { hyp := 344, conc := 343, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3459, conc := 3456, proof := sorry })
                      (RArray.leaf { hyp := 3459, conc := 3457, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3459, conc := 3458, proof := sorry })
                      (RArray.leaf { hyp := 3460, conc := 3455, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3461, conc := 3455, proof := sorry })
                      (RArray.leaf { hyp := 3462, conc := 3456, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3462, conc := 3460, proof := sorry })
                      (RArray.leaf { hyp := 3462, conc := 3461, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3463, conc := 3455, proof := sorry })
                      (RArray.leaf { hyp := 3464, conc := 3455, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3465, conc := 3456, proof := sorry })
                      (RArray.leaf { hyp := 3465, conc := 3463, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3465, conc := 3464, proof := sorry })
                      (RArray.leaf { hyp := 3466, conc := 3457, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3466, conc := 3460, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3466, conc := 3463, proof := sorry })
                      (RArray.leaf { hyp := 3467, conc := 3457, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3467, conc := 3461, proof := sorry })
                      (RArray.leaf { hyp := 3467, conc := 3464, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3468, conc := 3458, proof := sorry })
                      (RArray.leaf { hyp := 3468, conc := 3460, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3468, conc := 3464, proof := sorry })
                      (RArray.leaf { hyp := 345, conc := 324, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3469, conc := 3459, proof := sorry })
                      (RArray.leaf { hyp := 3469, conc := 3462, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3469, conc := 3465, proof := sorry })
                      (RArray.leaf { hyp := 3469, conc := 3466, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3469, conc := 3467, proof := sorry })
                      (RArray.leaf { hyp := 3469, conc := 3468, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3470, conc := 3455, proof := sorry })
                      (RArray.leaf { hyp := 3471, conc := 3455, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3473, conc := 3455, proof := sorry })
                      (RArray.leaf { hyp := 3474, conc := 3455, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3476, conc := 3457, proof := sorry })
                      (RArray.leaf { hyp := 3476, conc := 3473, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3480, conc := 3455, proof := sorry })
                      (RArray.leaf { hyp := 3481, conc := 3455, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3483, conc := 3455, proof := sorry })
                      (RArray.leaf { hyp := 3486, conc := 3457, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3486, conc := 3480, proof := sorry })
                      (RArray.leaf { hyp := 3487, conc := 3457, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3487, conc := 3481, proof := sorry })
                      (RArray.leaf { hyp := 3487, conc := 3484, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3488, conc := 3458, proof := sorry })
                      (RArray.leaf { hyp := 3488, conc := 3480, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3488, conc := 3484, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3489, conc := 3482, proof := sorry })
                      (RArray.leaf { hyp := 3489, conc := 3485, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3490, conc := 3460, proof := sorry })
                      (RArray.leaf { hyp := 3490, conc := 3470, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3490, conc := 3480, proof := sorry })
                      (RArray.leaf { hyp := 3494, conc := 3460, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3494, conc := 3473, proof := sorry })
                      (RArray.leaf { hyp := 3494, conc := 3483, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3495, conc := 3460, proof := sorry })
                      (RArray.leaf { hyp := 3495, conc := 3474, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3495, conc := 3484, proof := sorry })
                      (RArray.leaf { hyp := 3496, conc := 3461, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3496, conc := 3473, proof := sorry })
                      (RArray.leaf { hyp := 3496, conc := 3484, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3497, conc := 3462, proof := sorry })
                      (RArray.leaf { hyp := 3497, conc := 3475, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3497, conc := 3485, proof := sorry })
                      (RArray.leaf { hyp := 3497, conc := 3494, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3497, conc := 3495, proof := sorry })
                      (RArray.leaf { hyp := 3497, conc := 3496, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3498, conc := 3463, proof := sorry })
                      (RArray.leaf { hyp := 3498, conc := 3470, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3498, conc := 3483, proof := sorry })
                      (RArray.leaf { hyp := 348, conc := 313, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 348, conc := 345, proof := sorry })
                      (RArray.leaf { hyp := 33, conc := 24, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 33, conc := 30, proof := sorry })
                      (RArray.leaf { hyp := 3499, conc := 3463, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3499, conc := 3484, proof := sorry })
                      (RArray.leaf { hyp := 3500, conc := 3464, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3500, conc := 3470, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3500, conc := 3484, proof := sorry })
                      (RArray.leaf { hyp := 3501, conc := 3498, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3501, conc := 3500, proof := sorry })
                      (RArray.leaf { hyp := 3502, conc := 3466, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3502, conc := 3476, proof := sorry })
                      (RArray.leaf { hyp := 3502, conc := 3486, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3502, conc := 3490, proof := sorry })
                      (RArray.leaf { hyp := 3502, conc := 3494, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3503, conc := 3466, proof := sorry })
                      (RArray.leaf { hyp := 3503, conc := 3477, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3503, conc := 3487, proof := sorry })
                      (RArray.leaf { hyp := 3503, conc := 3491, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3503, conc := 3495, proof := sorry })
                      (RArray.leaf { hyp := 3504, conc := 3467, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3504, conc := 3476, proof := sorry })
                      (RArray.leaf { hyp := 3504, conc := 3487, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3504, conc := 3492, proof := sorry })
                      (RArray.leaf { hyp := 3504, conc := 3496, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3504, conc := 3500, proof := sorry })
                      (RArray.leaf { hyp := 3505, conc := 3468, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3505, conc := 3478, proof := sorry })
                      (RArray.leaf { hyp := 3505, conc := 3488, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3505, conc := 3490, proof := sorry })
                      (RArray.leaf { hyp := 3505, conc := 3495, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3505, conc := 3500, proof := sorry })
                      (RArray.leaf { hyp := 3506, conc := 3469, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3506, conc := 3479, proof := sorry })
                      (RArray.leaf { hyp := 3506, conc := 3489, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3506, conc := 3493, proof := sorry })
                      (RArray.leaf { hyp := 3506, conc := 3497, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3506, conc := 3502, proof := sorry })
                      (RArray.leaf { hyp := 3506, conc := 3503, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3506, conc := 3504, proof := sorry })
                      (RArray.leaf { hyp := 3506, conc := 3505, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3508, conc := 3455, proof := sorry })
                      (RArray.leaf { hyp := 349, conc := 334, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3509, conc := 3507, proof := sorry })
                      (RArray.leaf { hyp := 3510, conc := 3455, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3511, conc := 3455, proof := sorry })
                      (RArray.leaf { hyp := 3512, conc := 3456, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3512, conc := 3510, proof := sorry })
                      (RArray.leaf { hyp := 3512, conc := 3511, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3513, conc := 3507, proof := sorry })
                      (RArray.leaf { hyp := 3514, conc := 3457, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3514, conc := 3508, proof := sorry })
                      (RArray.leaf { hyp := 3514, conc := 3511, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3515, conc := 3507, proof := sorry })
                      (RArray.leaf { hyp := 3516, conc := 3509, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3516, conc := 3515, proof := sorry })
                      (RArray.leaf { hyp := 3517, conc := 3455, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3518, conc := 3455, proof := sorry })
                      (RArray.leaf { hyp := 350, conc := 335, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3519, conc := 3456, proof := sorry })
                      (RArray.leaf { hyp := 3519, conc := 3517, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3519, conc := 3518, proof := sorry })
                      (RArray.leaf { hyp := 3520, conc := 3455, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3521, conc := 3455, proof := sorry })
                      (RArray.leaf { hyp := 3522, conc := 3456, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3522, conc := 3520, proof := sorry })
                      (RArray.leaf { hyp := 3522, conc := 3521, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3523, conc := 3457, proof := sorry })
                      (RArray.leaf { hyp := 3523, conc := 3517, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3523, conc := 3520, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3524, conc := 3457, proof := sorry })
                      (RArray.leaf { hyp := 3524, conc := 3518, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3524, conc := 3521, proof := sorry })
                      (RArray.leaf { hyp := 3525, conc := 3458, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3525, conc := 3517, proof := sorry })
                      (RArray.leaf { hyp := 3525, conc := 3521, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3526, conc := 3459, proof := sorry })
                      (RArray.leaf { hyp := 3526, conc := 3519, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3526, conc := 3522, proof := sorry })
                      (RArray.leaf { hyp := 3526, conc := 3523, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3526, conc := 3524, proof := sorry })
                      (RArray.leaf { hyp := 3526, conc := 3525, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3527, conc := 3507, proof := sorry })
                      (RArray.leaf { hyp := 3528, conc := 3460, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3528, conc := 3508, proof := sorry })
                      (RArray.leaf { hyp := 3528, conc := 3518, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3529, conc := 3507, proof := sorry })
                      (RArray.leaf { hyp := 3530, conc := 3529, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3532, conc := 3460, proof := sorry })
                      (RArray.leaf { hyp := 3532, conc := 3511, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3532, conc := 3521, proof := sorry })
                      (RArray.leaf { hyp := 3533, conc := 3461, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3533, conc := 3510, proof := sorry })
                      (RArray.leaf { hyp := 3533, conc := 3521, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3534, conc := 3462, proof := sorry })
                      (RArray.leaf { hyp := 3534, conc := 3512, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3534, conc := 3522, proof := sorry })
                      (RArray.leaf { hyp := 3534, conc := 3531, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3534, conc := 3532, proof := sorry })
                      (RArray.leaf { hyp := 3534, conc := 3533, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3535, conc := 3507, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3536, conc := 3463, proof := sorry })
                      (RArray.leaf { hyp := 3536, conc := 3508, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3536, conc := 3521, proof := sorry })
                      (RArray.leaf { hyp := 3537, conc := 3507, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3538, conc := 3535, proof := sorry })
                      (RArray.leaf { hyp := 3538, conc := 3537, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 352, conc := 349, proof := sorry })
                      (RArray.leaf { hyp := 3539, conc := 3513, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3539, conc := 3527, proof := sorry })
                      (RArray.leaf { hyp := 3539, conc := 3535, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3540, conc := 3466, proof := sorry })
                      (RArray.leaf { hyp := 3540, conc := 3514, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3540, conc := 3524, proof := sorry })
                      (RArray.leaf { hyp := 3540, conc := 3528, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3540, conc := 3532, proof := sorry })
                      (RArray.leaf { hyp := 3540, conc := 3536, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3541, conc := 3529, proof := sorry })
                      (RArray.leaf { hyp := 3542, conc := 3515, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3543, conc := 3516, proof := sorry })
                      (RArray.leaf { hyp := 3543, conc := 3530, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3543, conc := 3534, proof := sorry })
                      (RArray.leaf { hyp := 3543, conc := 3538, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3543, conc := 3541, proof := sorry })
                      (RArray.leaf { hyp := 3543, conc := 3542, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3544, conc := 3455, proof := sorry })
                      (RArray.leaf { hyp := 3545, conc := 3455, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3547, conc := 3455, proof := sorry })
                      (RArray.leaf { hyp := 3548, conc := 3455, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 353, conc := 337, proof := sorry })
                      (RArray.leaf { hyp := 3552, conc := 3548, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3553, conc := 3546, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3554, conc := 3455, proof := sorry })
                      (RArray.leaf { hyp := 3555, conc := 3455, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3557, conc := 3455, proof := sorry })
                      (RArray.leaf { hyp := 354, conc := 346, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 354, conc := 350, proof := sorry })
                      (RArray.leaf { hyp := 3563, conc := 3556, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3563, conc := 3562, proof := sorry })
                      (RArray.leaf { hyp := 3565, conc := 3460, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3565, conc := 3545, proof := sorry })
                      (RArray.leaf { hyp := 3565, conc := 3555, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3566, conc := 3544, proof := sorry })
                      (RArray.leaf { hyp := 3566, conc := 3555, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3567, conc := 3564, proof := sorry })
                      (RArray.leaf { hyp := 3567, conc := 3566, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 355, conc := 347, proof := sorry })
                      (RArray.leaf { hyp := 3571, conc := 3570, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3572, conc := 3544, proof := sorry })
                      (RArray.leaf { hyp := 3572, conc := 3557, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3573, conc := 3558, proof := sorry })
                      (RArray.leaf { hyp := 3575, conc := 3574, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3576, conc := 3550, proof := sorry })
                      (RArray.leaf { hyp := 3576, conc := 3568, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3577, conc := 3551, proof := sorry })
                      (RArray.leaf { hyp := 3578, conc := 3570, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 356, conc := 341, proof := sorry })
                      (RArray.leaf { hyp := 3579, conc := 3562, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3580, conc := 3553, proof := sorry })
                      (RArray.leaf { hyp := 3580, conc := 3563, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3580, conc := 3567, proof := sorry })
                      (RArray.leaf { hyp := 3580, conc := 3571, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3580, conc := 3578, proof := sorry })
                      (RArray.leaf { hyp := 3580, conc := 3579, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3582, conc := 3470, proof := sorry })
                      (RArray.leaf { hyp := 3582, conc := 3508, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3582, conc := 3545, proof := sorry })
                      (RArray.leaf { hyp := 3586, conc := 3470, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3586, conc := 3511, proof := sorry })
                      (RArray.leaf { hyp := 3586, conc := 3548, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3587, conc := 3471, proof := sorry })
                      (RArray.leaf { hyp := 3587, conc := 3510, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3587, conc := 3548, proof := sorry })
                      (RArray.leaf { hyp := 3588, conc := 3549, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3588, conc := 3585, proof := sorry })
                      (RArray.leaf { hyp := 357, conc := 340, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 357, conc := 344, proof := sorry })
                      (RArray.leaf { hyp := 357, conc := 348, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 357, conc := 352, proof := sorry })
                      (RArray.leaf { hyp := 357, conc := 353, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3589, conc := 3547, proof := sorry })
                      (RArray.leaf { hyp := 3590, conc := 3473, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3590, conc := 3548, proof := sorry })
                      (RArray.leaf { hyp := 3592, conc := 3589, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3592, conc := 3591, proof := sorry })
                      (RArray.leaf { hyp := 3594, conc := 3551, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3594, conc := 3586, proof := sorry })
                      (RArray.leaf { hyp := 3597, conc := 3592, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3597, conc := 3593, proof := sorry })
                      (RArray.leaf { hyp := 3597, conc := 3595, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3597, conc := 3596, proof := sorry })
                      (RArray.leaf { hyp := 3599, conc := 3470, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3599, conc := 3518, proof := sorry })
                      (RArray.leaf { hyp := 3599, conc := 3555, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3600, conc := 3471, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3600, conc := 3517, proof := sorry })
                      (RArray.leaf { hyp := 3600, conc := 3555, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3601, conc := 3472, proof := sorry })
                      (RArray.leaf { hyp := 3601, conc := 3598, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3603, conc := 3558, proof := sorry })
                      (RArray.leaf { hyp := 3605, conc := 3602, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3605, conc := 3604, proof := sorry })
                      (RArray.leaf { hyp := 3606, conc := 3473, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3606, conc := 3557, proof := sorry })
                      (RArray.leaf { hyp := 3607, conc := 3558, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 359, conc := 358, proof := sorry })
                      (RArray.leaf { hyp := 3609, conc := 3608, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3610, conc := 3598, proof := sorry })
                      (RArray.leaf { hyp := 3611, conc := 3603, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3611, conc := 3607, proof := sorry })
                      (RArray.leaf { hyp := 3612, conc := 3608, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3613, conc := 3608, proof := sorry })
                      (RArray.leaf { hyp := 3614, conc := 3601, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3614, conc := 3610, proof := sorry })
                      (RArray.leaf { hyp := 3614, conc := 3613, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3615, conc := 3554, proof := sorry })
                      (RArray.leaf { hyp := 3616, conc := 3480, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3616, conc := 3508, proof := sorry })
                      (RArray.leaf { hyp := 3616, conc := 3555, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 360, conc := 358, proof := sorry })
                      (RArray.leaf { hyp := 3619, conc := 3480, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3619, conc := 3510, proof := sorry })
                      (RArray.leaf { hyp := 3619, conc := 3557, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3620, conc := 3558, proof := sorry })
                      (RArray.leaf { hyp := 3622, conc := 3512, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3622, conc := 3621, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3624, conc := 3558, proof := sorry })
                      (RArray.leaf { hyp := 3626, conc := 3623, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3626, conc := 3625, proof := sorry })
                      (RArray.leaf { hyp := 3628, conc := 3624, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 361, conc := 358, proof := sorry })
                      (RArray.leaf { hyp := 3629, conc := 3617, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3629, conc := 3621, proof := sorry })
                      (RArray.leaf { hyp := 3630, conc := 3562, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3630, conc := 3615, proof := sorry })
                      (RArray.leaf { hyp := 3631, conc := 3618, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3631, conc := 3622, proof := sorry })
                      (RArray.leaf { hyp := 3631, conc := 3627, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3633, conc := 3490, proof := sorry })
                      (RArray.leaf { hyp := 3633, conc := 3528, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3633, conc := 3565, proof := sorry })
                      (RArray.leaf { hyp := 3633, conc := 3582, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3633, conc := 3599, proof := sorry })
                      (RArray.leaf { hyp := 3633, conc := 3616, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3635, conc := 3617, proof := sorry })
                      (RArray.leaf { hyp := 3636, conc := 3632, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3637, conc := 3602, proof := sorry })
                      (RArray.leaf { hyp := 3638, conc := 3620, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 362, conc := 359, proof := sorry })
                      (RArray.leaf { hyp := 362, conc := 360, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 362, conc := 361, proof := sorry })
                      (RArray.leaf { hyp := 3639, conc := 3621, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3640, conc := 3621, proof := sorry })
                      (RArray.leaf { hyp := 3641, conc := 3622, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3641, conc := 3637, proof := sorry })
                      (RArray.leaf { hyp := 3643, conc := 3590, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3643, conc := 3624, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3644, conc := 3608, proof := sorry })
                      (RArray.leaf { hyp := 3645, conc := 3570, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3646, conc := 3609, proof := sorry })
                      (RArray.leaf { hyp := 3646, conc := 3642, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3647, conc := 3623, proof := sorry })
                      (RArray.leaf { hyp := 3648, conc := 3573, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 363, conc := 358, proof := sorry })
                      (RArray.leaf { hyp := 3649, conc := 3625, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3650, conc := 3581, proof := sorry })
                      (RArray.leaf { hyp := 3650, conc := 3625, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3651, conc := 3626, proof := sorry })
                      (RArray.leaf { hyp := 3651, conc := 3647, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3652, conc := 3632, proof := sorry })
                      (RArray.leaf { hyp := 3653, conc := 3594, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3653, conc := 3633, proof := sorry })
                      (RArray.leaf { hyp := 3653, conc := 3648, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3654, conc := 3612, proof := sorry })
                      (RArray.leaf { hyp := 3654, conc := 3634, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3654, conc := 3639, proof := sorry })
                      (RArray.leaf { hyp := 3655, conc := 3629, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3655, conc := 3635, proof := sorry })
                      (RArray.leaf { hyp := 3656, conc := 3613, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3656, conc := 3630, proof := sorry })
                      (RArray.leaf { hyp := 3656, conc := 3632, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3657, conc := 3580, proof := sorry })
                      (RArray.leaf { hyp := 3657, conc := 3597, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3657, conc := 3614, proof := sorry })
                      (RArray.leaf { hyp := 3657, conc := 3631, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3657, conc := 3636, proof := sorry })
                      (RArray.leaf { hyp := 3657, conc := 3641, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3657, conc := 3652, proof := sorry })
                      (RArray.leaf { hyp := 364, conc := 358, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3659, conc := 3658, proof := sorry })
                      (RArray.leaf { hyp := 3660, conc := 3658, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3661, conc := 3658, proof := sorry })
                      (RArray.leaf { hyp := 3662, conc := 3659, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3662, conc := 3660, proof := sorry })
                      (RArray.leaf { hyp := 3662, conc := 3661, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3663, conc := 3658, proof := sorry })
                      (RArray.leaf { hyp := 3664, conc := 3658, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3665, conc := 3659, proof := sorry })
                      (RArray.leaf { hyp := 3665, conc := 3663, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3665, conc := 3664, proof := sorry })
                      (RArray.leaf { hyp := 3666, conc := 3658, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3667, conc := 3658, proof := sorry })
                      (RArray.leaf { hyp := 3668, conc := 3659, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3668, conc := 3666, proof := sorry })
                      (RArray.leaf { hyp := 3668, conc := 3667, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3669, conc := 3660, proof := sorry })
                      (RArray.leaf { hyp := 3669, conc := 3663, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3669, conc := 3666, proof := sorry })
                      (RArray.leaf { hyp := 3670, conc := 3660, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3670, conc := 3664, proof := sorry })
                      (RArray.leaf { hyp := 3670, conc := 3667, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3671, conc := 3661, proof := sorry })
                      (RArray.leaf { hyp := 3671, conc := 3663, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3671, conc := 3667, proof := sorry })
                      (RArray.leaf { hyp := 3672, conc := 3662, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3672, conc := 3665, proof := sorry })
                      (RArray.leaf { hyp := 3672, conc := 3668, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3672, conc := 3669, proof := sorry })
                      (RArray.leaf { hyp := 3672, conc := 3670, proof := sorry })))))))))))

end EndToEnd
