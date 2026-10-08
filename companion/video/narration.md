# Narration script

These are the captions of the video with their start times. They are written to be read aloud, so the same text can be recorded as a voice-over. Each line should take no longer than the gap to the next start time.

| Start | Scene | Text |
| --- | --- | --- |
| 0:09 | CauchySchwarz | The Cauchy–Schwarz inequality says that the inner product of two vectors is never larger than the product of their lengths. |
| 0:18 | CauchySchwarz | The difference between the two sides is a gap. It measures how far apart the two vectors point. |
| 0:24 | CauchySchwarz | When the vectors turn towards each other the gap shrinks, and it is zero exactly when they are parallel. |
| 0:31 | CauchySchwarz | This video is about what happens to that gap when every entry of the vectors is raised to a power. |
| 0:39 | Powers | Raise every entry to a power p. Take the vectors (2, 1) and (1, 2). |
| 0:44 | Powers | Big entries grow faster than small ones, so as p increases the two vectors turn apart, towards the axes. |
| 0:51 | Powers | Johnston, Plosker, Torrance and Varona asked whether the gap of the powered vectors is at most the gap built from p-th powers. |
| 0:59 | Powers | At p = 1 and at p = 2 the two sides are equal. Between 1 and 2 the left side is bigger, so the inequality fails. |
| 1:07 | Powers | Beyond 2 the left side stays smaller. The question is whether this is true for every pair of vectors and every real p from 2 upwards. |
| 1:17 | History | The case p = 2 began as a question on MathOverflow in 2018, and it was proved a year later in work on quantum entanglement. |
| 1:25 | History | In 2025 Johnston, Plosker, Torrance and Varona proved it for every whole number p and showed that it fails between 1 and 2. |
| 1:34 | History | They tested real exponents on more than ten billion random pairs and conjectured that every real p from 2 upwards works. |
| 1:42 | History | This is Conjecture 5.1 of their paper, and it is now a theorem. |
| 1:48 | Tensor | For p = 2, write the products of all pairs of entries in a grid. This is the tensor square of v. |
| 1:55 | Tensor | Its diagonal is exactly the vector of squares, v². |
| 1:58 | Tensor | The full grids have inner product ⟨v, w⟩², so the right side of the inequality is the gap of the full grids. |
| 2:06 | Tensor | Keeping only the diagonal entries can only shrink the gap. The same works with p factors for any whole number p. |
| 2:14 | Tensor | For p = 2.5 there is no grid with two and a half factors. A different idea is needed. |
| 2:21 | Matrices | For each coordinate i, put the numbers v_i², v_i w_i and w_i² into a two by two matrix. |
| 2:27 | Matrices | For v = (2, 1) and w = (1, 2) there are two of them. Adding them gives a matrix of the lengths and the inner product of v and w. |
| 2:36 | Matrices | Raise every entry to the power p. If you power first and then add, you get the left side's matrix. If you add first and then power, you get the right side's matrix. |
| 2:48 | Matrices | The key fact: for p at least 2, adding and then powering always gives the bigger matrix. |
| 2:54 | Matrices | Bigger means that the difference is positive semidefinite: its diagonal is nonnegative and its corner entry is at most the geometric mean of the diagonal. |
| 3:05 | Matrices | This is a case of a 2015 theorem of Guillot, Khare and Rajaratnam, and its threshold is exactly 2. |
| 3:16 | Cone | The positive semidefinite two by two matrices form a round cone. Up is the average of the diagonal, and the two sideways directions are the rest. |
| 3:26 | Cone | The dot is the difference between the two matrices for v = (2, 1) and w = (1, 2). For p between 1 and 2 it lies outside the cone. |
| 3:34 | Cone | At p = 2 it touches the boundary, and for every larger p it stays inside. |
| 3:41 | Cone | The proof shows that for p at least 2 this happens for every pair of vectors, using a double integral formula for the powers. |
| 3:51 | Phi | One last ingredient turns a matrix into a number: the square root of the diagonal product, minus the corner. |
| 3:59 | Phi | Applied to the two matrices, it gives exactly the two sides of the inequality. |
| 4:04 | Phi | And it only grows when its input moves up the cone. So the bigger matrix has the bigger gap, and the inequality is proved. |
| 4:14 | NewResults | The paper also finds every case of equality. For p above 2 only the obvious ones remain. For p = 2 there is one extra family. |
| 4:23 | NewResults | Weights can be put on the coordinates. The weighted inequality holds for every p ≥ 2 exactly when every product of two different weights is at least 1. |
| 4:35 | Lean | Every step is also checked in Lean 4, a proof assistant, with the Mathlib library. This is the conjecture exactly as it is stated there. |
| 4:44 | Lean | The check script confirms there are no gaps and no extra assumptions. The equality cases and the weighted result are checked too. |
| 4:55 | Applications | Take two probability distributions, for example a physical system with two different energy functions. |
| 5:02 | Applications | Raising every probability to a power p and renormalising is the same as cooling the system by a factor p. The distributions sharpen and their overlap falls. |
| 5:12 | Applications | Applied to the square roots of the probabilities, the theorem limits how much the overlap can fall, for every cooling factor of 2 or more. |
| 5:22 | Applications | Semi-supervised learning sharpens predictions in the same way. UDA uses temperature 0.4, which is p = 2.5, a case that needs the new theorem. |
| 5:32 | Outro | So the conjecture is true, the threshold 2 comes from two by two matrices, and the whole argument is checked by computer. |
| 5:41 | Outro | Thank you for watching. The paper, the Lean code and an applications report are linked below. |

Total length: 5:48.
