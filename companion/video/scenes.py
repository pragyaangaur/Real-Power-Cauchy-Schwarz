"""Animated exposition of the real-power Cauchy-Schwarz inequality.

Render every scene and assemble the film with build.sh. Each scene logs the time at which
each caption appears, so build.sh can also write a subtitle file and a narration script.
"""

import json
from pathlib import Path

import numpy as np
from manim import *

BG = "#0E1621"
FG = "#E8ECF2"
MUTED = "#8A97A8"
FAINT = "#22324A"
VCOL = "#F2A65A"
WCOL = "#5CC8D7"
GOOD = "#7BD389"
BAD = "#F2545B"
GOLD = "#F4D35E"
FONT = "Avenir Next"
MONO = "Menlo"

LOG_DIR = Path(__file__).resolve().parent / "captions"
LOG_DIR.mkdir(exist_ok=True)

config.background_color = BG
MathTex.set_default(color=FG)
Tex.set_default(color=FG)


def wrap(text, width=72):
    lines, line = [], ""
    for word in text.split():
        if len(line) + len(word) + 1 > width and line:
            lines.append(line)
            line = word
        else:
            line = f"{line} {word}".strip()
    lines.append(line)
    return "\n".join(lines)


def label(text, size=28, color=FG, weight=NORMAL):
    return Text(text, font=FONT, font_size=size, color=color, weight=weight)


class Captioned:
    """Mixin that shows narration captions and logs when they appear."""

    def init_captions(self):
        self.caption = None
        self.caption_start = 0.0
        self.caption_need = 0.0
        self.caption_log = []

    def now(self):
        return self.renderer.time

    def cap(self, text, fixed=False):
        # Keep the previous caption on screen long enough to be read.
        if self.caption is not None:
            left = self.caption_need - (self.now() - self.caption_start)
            if left > 0:
                self.wait(left)
        new = Text(wrap(text), font=FONT, font_size=27, color=FG, line_spacing=0.9)
        new.to_edge(DOWN, buff=0.35)
        back = BackgroundRectangle(new, color=BG, fill_opacity=0.85, buff=0.15)
        group = VGroup(back, new)
        if fixed:
            self.add_fixed_in_frame_mobjects(group)
        if self.caption is None:
            self.play(FadeIn(group, run_time=0.4))
        else:
            self.play(FadeOut(self.caption, run_time=0.25), FadeIn(group, run_time=0.25))
        self.caption = group
        self.caption_start = self.now()
        self.caption_need = max(2.6, len(text) / 15.0)
        self.caption_log.append({"t": round(self.caption_start, 2), "text": text})

    def end_caption(self):
        if self.caption is not None:
            left = self.caption_need - (self.now() - self.caption_start)
            if left > 0:
                self.wait(left)

    def save_captions(self):
        self.end_caption()
        self.caption_log.append({"t": round(self.now(), 2), "text": None})
        (LOG_DIR / f"{type(self).__name__}.json").write_text(json.dumps(self.caption_log, indent=1))

    def clear(self, keep_caption=True):
        if not keep_caption:
            self.end_caption()
        mobs = [m for m in self.mobjects if m is not self.caption or not keep_caption]
        if mobs:
            self.play(*[FadeOut(m) for m in mobs], run_time=0.6)
        if not keep_caption:
            self.caption = None


class Base(Captioned, Scene):
    def setup(self):
        self.init_captions()

    def tear_down(self):
        self.save_captions()


class Base3D(Captioned, ThreeDScene):
    def setup(self):
        self.init_captions()

    def tear_down(self):
        self.save_captions()


# 1. Title ----------------------------------------------------------------------------------

class S01Title(Base):
    def construct(self):
        kicker = label("A 2025 CONJECTURE, PROVED AND CHECKED BY COMPUTER", 22, MUTED)
        title = label("Cauchy–Schwarz for real powers", 54, FG, BOLD)
        formula = MathTex(
            r"\|v^p\|\,\|w^p\|-\langle v^p,w^p\rangle", r"\;\le\;", r"\|v\|^p\|w\|^p-\langle v,w\rangle^p",
            font_size=46,
        )
        formula[0].set_color(VCOL)
        formula[2].set_color(WCOL)
        cond = MathTex(r"v,w\ge0,\qquad p\ge 2 \text{ real}", font_size=34, color=MUTED)
        author = label("Pragyaan Gaur", 26, MUTED)
        group = VGroup(kicker, title, formula, cond, author).arrange(DOWN, buff=0.45)
        group.shift(UP * 0.4)
        self.play(FadeIn(kicker, shift=DOWN * 0.2), Write(title), run_time=1.6)
        self.play(Write(formula), run_time=2.2)
        self.play(FadeIn(cond), FadeIn(author), run_time=0.8)
        self.wait(2.6)
        self.play(FadeOut(group), run_time=0.8)


# 2. Cauchy-Schwarz ---------------------------------------------------------------------------

class S02CauchySchwarz(Base):
    def construct(self):
        origin = LEFT * 4.2 + DOWN * 1.4
        unit = 1.0
        theta = ValueTracker(70 * DEGREES)
        a_v, len_v, len_w = 15 * DEGREES, 3.4, 2.8

        axes = VGroup(
            Line(origin + LEFT * 0.4, origin + RIGHT * 4.2, color=FAINT, stroke_width=2),
            Line(origin + DOWN * 0.4, origin + UP * 3.6, color=FAINT, stroke_width=2),
        )
        v = Arrow(origin, origin + len_v * unit * np.array([np.cos(a_v), np.sin(a_v), 0]), buff=0, color=VCOL, stroke_width=7)
        w = always_redraw(
            lambda: Arrow(
                origin,
                origin + len_w * unit * np.array([np.cos(theta.get_value()), np.sin(theta.get_value()), 0]),
                buff=0, color=WCOL, stroke_width=7,
            )
        )
        lv = MathTex("v", color=VCOL, font_size=44).next_to(v.get_end(), RIGHT, buff=0.15)
        lw = always_redraw(lambda: MathTex("w", color=WCOL, font_size=44).next_to(w.get_end(), UP, buff=0.12))
        arc = always_redraw(
            lambda: Arc(radius=0.8, start_angle=a_v, angle=theta.get_value() - a_v, arc_center=origin, color=MUTED)
        )

        cs = MathTex(r"\langle v,w\rangle", r"\;\le\;", r"\|v\|\,\|w\|", font_size=56).move_to(RIGHT * 2.6 + UP * 2.3)
        w0 = w.copy()
        self.play(Create(axes), GrowArrow(v), GrowArrow(w0), run_time=1.2)
        self.remove(w0)
        self.add(w, lv, lw, arc)
        self.cap("The Cauchy–Schwarz inequality says that the inner product of two vectors is never larger than the product of their lengths.")
        self.play(Write(cs), run_time=1.5)

        gap_lbl = MathTex(r"\text{gap}=\|v\|\,\|w\|-\langle v,w\rangle", font_size=40).next_to(cs, DOWN, buff=0.7)
        gap_val = lambda: len_v * len_w * (1 - np.cos(theta.get_value() - a_v))
        bar_base = RIGHT * 0.9 + DOWN * 0.9
        bar = always_redraw(
            lambda: Rectangle(width=max(0.001, 0.45 * gap_val()), height=0.45, fill_color=GOLD, fill_opacity=0.9, stroke_width=0).move_to(bar_base, aligned_edge=LEFT)
        )
        num = always_redraw(lambda: DecimalNumber(gap_val(), num_decimal_places=2, font_size=36, color=GOLD).next_to(bar, RIGHT, buff=0.2))
        self.cap("The difference between the two sides is a gap. It measures how far apart the two vectors point.")
        self.play(Write(gap_lbl), FadeIn(bar), FadeIn(num))
        self.play(theta.animate.set_value(100 * DEGREES), run_time=2.5)
        self.cap("When the vectors turn towards each other the gap shrinks, and it is zero exactly when they are parallel.")
        self.play(theta.animate.set_value(a_v), run_time=3.5, rate_func=smooth)
        self.wait(0.5)
        self.play(theta.animate.set_value(60 * DEGREES), run_time=1.5)
        self.cap("This video is about what happens to that gap when every entry of the vectors is raised to a power.")
        self.wait(1)
        self.clear(keep_caption=False)


# 3. Powers -----------------------------------------------------------------------------------

def sides(p):
    """Left and right side for v = (2, 1), w = (1, 2)."""
    return (2**p - 1) ** 2, 5**p - 4**p


class S03Powers(Base):
    def construct(self):
        p = ValueTracker(1.0)
        ineq = MathTex(
            r"\|v^p\|\,\|w^p\|-\langle v^p,w^p\rangle", r"\;\le\;", r"\|v\|^p\|w\|^p-\langle v,w\rangle^p",
            font_size=44,
        ).to_edge(UP, buff=0.5)
        ineq[0].set_color(VCOL)
        ineq[2].set_color(WCOL)
        under_l = label("gap of the powered vectors", 22, VCOL).next_to(ineq[0], DOWN, buff=0.2)
        under_r = label("p-th powers of the original numbers", 22, WCOL).next_to(ineq[2], DOWN, buff=0.2)

        ex = MathTex(r"v=(2,1),\quad w=(1,2)", font_size=38).move_to(LEFT * 4.3 + UP * 1.55)
        vp = always_redraw(lambda: MathTex(
            rf"v^p=({2**p.get_value():.2f},\,1),\ \ w^p=(1,\,{2**p.get_value():.2f})", font_size=30, color=MUTED
        ).next_to(ex, DOWN, buff=0.25))

        origin = LEFT * 5.6 + DOWN * 1.85
        def arrow(x, y, col):
            d = np.array([x, y, 0.0])
            d = 2.4 * d / np.linalg.norm(d)
            return Arrow(origin, origin + d, buff=0, color=col, stroke_width=6)
        va = always_redraw(lambda: arrow(2 ** p.get_value(), 1, VCOL))
        wa = always_redraw(lambda: arrow(1, 2 ** p.get_value(), WCOL))
        frame = VGroup(
            Line(origin, origin + RIGHT * 2.7, color=FAINT), Line(origin, origin + UP * 2.7, color=FAINT)
        )

        self.cap("Raise every entry to a power p. Take the vectors (2, 1) and (1, 2).")
        self.play(Write(ex), FadeIn(vp), Create(frame), FadeIn(va), FadeIn(wa))
        self.cap("Big entries grow faster than small ones, so as p increases the two vectors turn apart, towards the axes.")
        self.play(p.animate.set_value(3.0), run_time=3.5)
        self.play(p.animate.set_value(1.0), run_time=1.5)

        self.cap("Johnston, Plosker, Torrance and Varona asked whether the gap of the powered vectors is at most the gap built from p-th powers.")
        self.play(Write(ineq), run_time=2)
        self.play(FadeIn(under_l), FadeIn(under_r))

        ax = Axes(
            x_range=[1, 3, 0.5], y_range=[0.75, 1.1, 0.05], x_length=6.2, y_length=2.9,
            axis_config={"color": MUTED, "include_tip": False, "font_size": 24},
            x_axis_config={"numbers_to_include": [1, 1.5, 2, 2.5, 3]},
        ).move_to(RIGHT * 2.8 + DOWN * 0.35)
        one = DashedLine(ax.c2p(1, 1), ax.c2p(3, 1), color=MUTED)
        ylab = label("left side ÷ right side", 22, MUTED).next_to(ax, UP, buff=0.1).align_to(ax, LEFT)
        xlab = MathTex("p", font_size=30, color=MUTED).next_to(ax.x_axis, RIGHT, buff=0.1)
        bad_zone = Polygon(ax.c2p(1, 1), ax.c2p(3, 1), ax.c2p(3, 1.1), ax.c2p(1, 1.1), stroke_width=0, fill_color=BAD, fill_opacity=0.12)
        bad_lbl = label("fails", 22, BAD).move_to(ax.c2p(2.75, 1.06))
        ratio = lambda q: sides(q)[0] / sides(q)[1]
        curve = always_redraw(lambda: ax.plot(ratio, x_range=[1.0001, max(1.002, p.get_value())], color=GOLD, stroke_width=5))
        dot = always_redraw(lambda: Dot(ax.c2p(p.get_value(), ratio(max(1.0001, p.get_value()))), color=BAD if ratio(max(1.0001, p.get_value())) > 1 + 1e-9 else GOOD, radius=0.09))
        pread = always_redraw(lambda: MathTex(rf"p={p.get_value():.2f}", font_size=36, color=GOLD).next_to(ax, LEFT, buff=0.5).shift(UP * 0.8))

        self.play(Create(ax), FadeIn(one), FadeIn(ylab), FadeIn(xlab), FadeIn(bad_zone), FadeIn(bad_lbl))
        self.add(curve, dot, pread)
        self.cap("At p = 1 and at p = 2 the two sides are equal. Between 1 and 2 the left side is bigger, so the inequality fails.")
        self.play(p.animate.set_value(2.0), run_time=5, rate_func=linear)
        self.cap("Beyond 2 the left side stays smaller. The question is whether this is true for every pair of vectors and every real p from 2 upwards.")
        self.play(p.animate.set_value(3.0), run_time=4, rate_func=linear)
        self.wait(1)
        self.clear(keep_caption=False)


# 4. History ----------------------------------------------------------------------------------

class S04History(Base):
    def construct(self):
        events = [
            ("2018", "Johnston asks on MathOverflow about the case p = 2"),
            ("2019", "Johnston and MacLean prove it, from quantum entanglement theory"),
            ("2025", "Johnston, Plosker, Torrance and Varona: every whole number p works,\n1 < p < 2 fails, real p ≥ 2 conjectured after 10¹⁰ random tests"),
            ("2026", "Proved for every real p ≥ 2, with all cases of equality"),
        ]
        rows = VGroup()
        for year, text in events:
            y = label(year, 30, GOLD, BOLD)
            t = label(text, 24, FG)
            rows.add(VGroup(y, t).arrange(RIGHT, buff=0.5, aligned_edge=UP))
        rows.arrange(DOWN, buff=0.45, aligned_edge=LEFT).to_edge(UP, buff=0.6).to_edge(LEFT, buff=0.9)
        self.cap("The case p = 2 began as a question on MathOverflow in 2018, and it was proved a year later in work on quantum entanglement.")
        self.play(FadeIn(rows[0], shift=RIGHT * 0.3))
        self.play(FadeIn(rows[1], shift=RIGHT * 0.3))
        self.cap("In 2025 Johnston, Plosker, Torrance and Varona proved it for every whole number p and showed that it fails between 1 and 2.")
        self.play(FadeIn(rows[2], shift=RIGHT * 0.3))

        line = NumberLine(x_range=[0, 4.5, 1], length=10, color=MUTED, include_numbers=True, font_size=26).shift(DOWN * 1.6)
        red1 = Line(line.n2p(0), line.n2p(1), color=BAD, stroke_width=10)
        red2 = Line(line.n2p(1), line.n2p(2), color=BAD, stroke_width=10)
        open_ = Line(line.n2p(2), line.n2p(4.5), color=MUTED, stroke_width=10)
        dots = VGroup(*[Dot(line.n2p(k), color=GOOD, radius=0.12) for k in (1, 2, 3, 4)])
        q = label("?", 40, GOLD, BOLD).next_to(line.n2p(3.25), UP, buff=0.3)
        self.play(Create(line))
        self.play(Create(red1), Create(red2), FadeIn(dots))
        self.cap("They tested real exponents on more than ten billion random pairs and conjectured that every real p from 2 upwards works.")
        self.play(Create(open_), FadeIn(q))
        self.wait(1)
        self.cap("This is Conjecture 5.1 of their paper, and it is now a theorem.")
        self.play(FadeIn(rows[3], shift=RIGHT * 0.3))
        green = Line(line.n2p(2), line.n2p(4.5), color=GOOD, stroke_width=10)
        self.play(Transform(open_, green), FadeOut(q), run_time=1.5)
        self.wait(1.5)
        self.clear(keep_caption=False)


# 5. Tensor powers ----------------------------------------------------------------------------

class S05Tensor(Base):
    def construct(self):
        title = label("Why whole numbers were easier", 34, GOLD, BOLD).to_edge(UP, buff=0.5)
        self.play(FadeIn(title))
        entries = [[f"v_{i}v_{j}" for j in (1, 2, 3)] for i in (1, 2, 3)]
        mat = Matrix(entries, element_to_mobject_config={"font_size": 42, "color": FG}, h_buff=1.35)
        mat.get_brackets().set_color(FG)
        grid = VGroup(MathTex(r"v\otimes v=", font_size=44), mat).arrange(RIGHT, buff=0.25).shift(LEFT * 3 + UP * 0.6)
        self.cap("For p = 2, write the products of all pairs of entries in a grid. This is the tensor square of v.")
        self.play(Write(grid), run_time=2)
        cells = mat.get_entries()
        boxes = VGroup(*[SurroundingRectangle(cells[4 * k], color=GOLD, buff=0.1) for k in range(3)])
        diag = MathTex(r"v^2=(v_1^2,\,v_2^2,\,v_3^2)", font_size=44, color=VCOL).shift(RIGHT * 3.6 + UP * 1.4)
        self.cap("Its diagonal is exactly the vector of squares, v².")
        self.play(Create(boxes), run_time=1.2)
        self.play(TransformFromCopy(boxes, diag), run_time=1.2)

        facts = VGroup(
            MathTex(r"\langle v\otimes v,\;w\otimes w\rangle=\langle v,w\rangle^2", font_size=36),
            MathTex(r"\|v\otimes v\|=\|v\|^2", font_size=36),
        ).arrange(DOWN, buff=0.3).next_to(diag, DOWN, buff=0.6)
        self.cap("The full grids have inner product ⟨v, w⟩², so the right side of the inequality is the gap of the full grids.")
        self.play(Write(facts), run_time=1.8)
        concl = label("Keeping only the diagonal can only shrink the gap.", 28, GOOD).shift(DOWN * 2.1)
        self.cap("Keeping only the diagonal entries can only shrink the gap. The same works with p factors for any whole number p.")
        self.play(FadeIn(concl))
        self.wait(1)
        self.cap("For p = 2.5 there is no grid with two and a half factors. A different idea is needed.")
        cross = Cross(grid, stroke_color=BAD, stroke_width=8)
        q = MathTex(r"v^{\otimes 2.5}\;?", font_size=56, color=BAD).move_to(grid)
        self.play(Create(cross))
        self.play(FadeOut(grid), FadeOut(boxes), FadeOut(cross), FadeIn(q))
        self.wait(1.2)
        self.clear(keep_caption=False)


# 6. Two-by-two matrices ----------------------------------------------------------------------

class S06Matrices(Base):
    def construct(self):
        title = label("The new idea: one small matrix per coordinate", 34, GOLD, BOLD).to_edge(UP, buff=0.5)
        self.play(FadeIn(title))
        gen = MathTex(
            r"A_i=\begin{pmatrix} v_i^2 & v_iw_i\\ v_iw_i & w_i^2\end{pmatrix}", font_size=44
        ).shift(UP * 1.6)
        self.cap("For each coordinate i, put the numbers v_i², v_i w_i and w_i² into a two by two matrix.")
        self.play(Write(gen))
        ex = MathTex(
            r"A_1=\begin{pmatrix}4&2\\2&1\end{pmatrix}", r"\quad", r"A_2=\begin{pmatrix}1&2\\2&4\end{pmatrix}",
            r"\quad\Longrightarrow\quad", r"A_1+A_2=\begin{pmatrix}5&4\\4&5\end{pmatrix}",
            font_size=38,
        ).next_to(gen, DOWN, buff=0.55)
        self.cap("For v = (2, 1) and w = (1, 2) there are two of them. Adding them gives a matrix of the lengths and the inner product of v and w.")
        self.play(Write(ex[:3]))
        self.play(Write(ex[3:]))

        r1 = MathTex(r"\text{power, then add:}\ \ A_1^{\circ p}+A_2^{\circ p}=\begin{pmatrix}\|v^p\|^2&\langle v^p,w^p\rangle\\ \langle v^p,w^p\rangle&\|w^p\|^2\end{pmatrix}", font_size=34, color=VCOL)
        r2 = MathTex(r"\text{add, then power:}\ \ (A_1+A_2)^{\circ p}=\begin{pmatrix}\|v\|^{2p}&\langle v,w\rangle^p\\ \langle v,w\rangle^p&\|w\|^{2p}\end{pmatrix}", font_size=34, color=WCOL)
        routes = VGroup(r1, r2).arrange(DOWN, buff=0.35).next_to(ex, DOWN, buff=0.5)
        self.cap("Raise every entry to the power p. If you power first and then add, you get the left side's matrix. If you add first and then power, you get the right side's matrix.")
        self.play(FadeOut(gen), ex.animate.shift(UP * 1.6))
        routes.next_to(ex, DOWN, buff=0.5)
        self.play(Write(r1), run_time=1.6)
        self.play(Write(r2), run_time=1.6)
        self.wait(1)
        self.end_caption()
        self.play(FadeOut(ex), FadeOut(routes), FadeOut(title))
        lemma = MathTex(r"(A+B)^{\circ p}\;\succeq\;A^{\circ p}+B^{\circ p}\qquad (p\ge 2)", font_size=50, color=GOLD).shift(UP * 1.2)
        self.cap("The key fact: for p at least 2, adding and then powering always gives the bigger matrix.")
        self.play(Write(lemma), run_time=1.8)
        psd = MathTex(
            r"\begin{pmatrix}a&c\\c&b\end{pmatrix}\succeq 0\iff a\ge0,\ b\ge0,\ c^2\le ab",
            font_size=40,
        ).next_to(lemma, DOWN, buff=0.7)
        self.cap("Bigger means that the difference is positive semidefinite: its diagonal is nonnegative and its corner entry is at most the geometric mean of the diagonal.")
        self.play(Write(psd), run_time=1.8)
        cite = label("Guillot, Khare and Rajaratnam (2015): this holds for p in {1} ∪ [2, ∞) and fails between 1 and 2.", 24, MUTED).next_to(psd, DOWN, buff=0.6)
        self.cap("This is a case of a 2015 theorem of Guillot, Khare and Rajaratnam, and its threshold is exactly 2.")
        self.play(FadeIn(cite))
        self.wait(1.5)
        self.clear(keep_caption=False)


# 7. The cone ---------------------------------------------------------------------------------

def diff_matrix(p):
    """Gram(v,w)^p - Gram(v^p,w^p) for v = (2, 1), w = (1, 2), as (a, b, c)."""
    a = 5**p - (4**p + 1)
    c = 4**p - 2 * 2**p
    return a, a, c


class S07Cone(Base3D):
    def construct(self):
        self.set_camera_orientation(phi=72 * DEGREES, theta=-50 * DEGREES, zoom=1.3, frame_center=OUT * 0.9)
        cone = Surface(
            lambda u, t: np.array([u * np.cos(t), u * np.sin(t), u]),
            u_range=[0, 2.6], v_range=[0, TAU], resolution=(16, 40),
            fill_color=GOOD, fill_opacity=0.18, stroke_color=GOOD, stroke_width=0.6, stroke_opacity=0.5,
        )
        axes = ThreeDAxes(x_range=[-3, 3], y_range=[-3, 3], z_range=[0, 3], x_length=6, y_length=6, z_length=3, axis_config={"color": FAINT})
        title = label("The cone of positive semidefinite 2×2 matrices", 30, GOLD, BOLD).to_edge(UP, buff=0.4)
        self.add_fixed_in_frame_mobjects(title)
        self.play(FadeIn(title), Create(axes), run_time=1)
        self.play(Create(cone), run_time=2)
        self.cap("The positive semidefinite two by two matrices form a round cone. Up is the average of the diagonal, and the two sideways directions are the rest.", fixed=True)
        self.begin_ambient_camera_rotation(rate=0.06)

        p = ValueTracker(1.2)

        def point(q):
            a, b, c = diff_matrix(q)
            vec = np.array([(a - b) / 2, c, (a + b) / 2])
            return 2.3 * vec / np.linalg.norm(vec)

        def inside(q):
            a, b, c = diff_matrix(q)
            return a >= 0 and c * c <= a * b * (1 + 1e-12)

        dot = always_redraw(lambda: Dot3D(point(p.get_value()), radius=0.14, color=GOOD if inside(p.get_value()) else BAD))
        ray = always_redraw(lambda: Line3D(ORIGIN, point(p.get_value()), thickness=0.015, color=GOOD if inside(p.get_value()) else BAD))
        trail = TracedPath(lambda: point(p.get_value()), stroke_color=GOLD, stroke_width=3)
        self.add(trail, ray, dot)
        pread = always_redraw(lambda: MathTex(rf"p={p.get_value():.2f}", font_size=40, color=GOOD if inside(p.get_value()) else BAD).to_corner(UR, buff=0.6).shift(DOWN * 0.8))
        self.add_fixed_in_frame_mobjects(pread)
        self.add(pread)
        self.cap("The dot is the difference between the two matrices for v = (2, 1) and w = (1, 2). For p between 1 and 2 it lies outside the cone.", fixed=True)
        self.play(p.animate.set_value(1.95), run_time=5, rate_func=linear)
        self.cap("At p = 2 it touches the boundary, and for every larger p it stays inside.", fixed=True)
        self.play(p.animate.set_value(2.0), run_time=1.5, rate_func=linear)
        self.wait(0.5)
        self.play(p.animate.set_value(3.2), run_time=4, rate_func=linear)
        self.cap("The proof shows that for p at least 2 this happens for every pair of vectors, using a double integral formula for the powers.", fixed=True)
        self.wait(1)
        self.end_caption()
        self.stop_ambient_camera_rotation()
        self.play(*[FadeOut(m) for m in self.mobjects], run_time=0.8)
        self.caption = None


# 8. From matrices back to numbers -------------------------------------------------------------

class S08Phi(Base):
    def construct(self):
        title = label("From matrices back to numbers", 34, GOLD, BOLD).to_edge(UP, buff=0.5)
        self.play(FadeIn(title))
        phi = MathTex(r"\Phi\begin{pmatrix}a&c\\c&b\end{pmatrix}=\sqrt{ab}-c", font_size=52).shift(UP * 1.5)
        self.cap("One last ingredient turns a matrix into a number: the square root of the diagonal product, minus the corner.")
        self.play(Write(phi))
        l = MathTex(r"\Phi(\text{power, then add})", r"=", r"\|v^p\|\,\|w^p\|-\langle v^p,w^p\rangle", font_size=38)
        r = MathTex(r"\Phi(\text{add, then power})", r"=", r"\|v\|^p\|w\|^p-\langle v,w\rangle^p", font_size=38)
        l[2].set_color(VCOL)
        r[2].set_color(WCOL)
        both = VGroup(l, r).arrange(DOWN, buff=0.35, aligned_edge=LEFT).next_to(phi, DOWN, buff=0.6)
        self.cap("Applied to the two matrices, it gives exactly the two sides of the inequality.")
        self.play(Write(l), run_time=1.5)
        self.play(Write(r), run_time=1.5)
        mono = MathTex(r"M\preceq N\ \Longrightarrow\ \Phi(M)\le\Phi(N)", font_size=44, color=GOLD).next_to(both, DOWN, buff=0.6)
        self.cap("And it only grows when its input moves up the cone. So the bigger matrix has the bigger gap, and the inequality is proved.")
        self.play(Write(mono), run_time=1.5)
        qed = label("∎", 48, GOLD).next_to(mono, RIGHT, buff=0.5)
        self.play(FadeIn(qed, scale=1.5))
        self.wait(1.5)
        self.clear(keep_caption=False)


# 9. New results ------------------------------------------------------------------------------

class S09NewResults(Base):
    def construct(self):
        title = label("Beyond the conjecture", 34, GOLD, BOLD).to_edge(UP, buff=0.5)
        self.play(FadeIn(title))
        eq_head = label("When are the two sides equal?", 28, FG, BOLD).move_to(LEFT * 3.4 + UP * 2.55)
        eq1 = VGroup(
            MathTex(r"p>2:", font_size=34, color=GOLD),
            label("v and w are parallel, or each has\nonly one nonzero entry", 27),
        ).arrange(RIGHT, buff=0.3, aligned_edge=UP)
        eq2 = VGroup(
            MathTex(r"p=2:", font_size=34, color=GOLD),
            label("one more family, for example\nv = (1, 2) and w = (4, 2)", 27),
        ).arrange(RIGHT, buff=0.3, aligned_edge=UP)
        eqs = VGroup(eq1, eq2).arrange(DOWN, buff=0.45, aligned_edge=LEFT).next_to(eq_head, DOWN, buff=0.4).align_to(eq_head, LEFT)
        self.cap("The paper also finds every case of equality. For p above 2 only the obvious ones remain. For p = 2 there is one extra family.")
        self.play(FadeIn(eq_head), FadeIn(eq1))
        self.play(FadeIn(eq2))

        w_head = label("Weighted versions", 28, FG, BOLD).move_to(RIGHT * 3.3 + UP * 2.55)
        ax = Axes(x_range=[0, 3, 1], y_range=[0, 3, 1], x_length=2.7, y_length=2.7, axis_config={"color": MUTED, "include_tip": False, "font_size": 20}, x_axis_config={"numbers_to_include": [1, 2, 3]}, y_axis_config={"numbers_to_include": [1, 2, 3]}).next_to(w_head, DOWN, buff=0.35)
        region = ax.get_area(ax.plot(lambda x: 1 / x, x_range=[1 / 3, 3]), x_range=[1 / 3, 3], bounded_graph=ax.plot(lambda x: 3, x_range=[1 / 3, 3]), color=GOOD, opacity=0.3)
        hyper = ax.plot(lambda x: 1 / x, x_range=[1 / 3, 3], color=GOOD)
        cond = MathTex(r"\omega_i\,\omega_j\ge 1\ \text{ for all } i\ne j", font_size=32, color=GOOD).next_to(ax, DOWN, buff=0.25)
        self.cap("Weights can be put on the coordinates. The weighted inequality holds for every p ≥ 2 exactly when every product of two different weights is at least 1.")
        self.play(FadeIn(w_head), Create(ax))
        self.play(FadeIn(region), Create(hyper), Write(cond))
        self.wait(2)
        self.clear(keep_caption=False)


# 10. Lean --------------------------------------------------------------------------------------

class S10Lean(Base):
    def construct(self):
        title = label("Checked by a computer", 34, GOLD, BOLD).to_edge(UP, buff=0.5)
        self.play(FadeIn(title))
        code = (
            "def Conjecture_5_1 : Prop :=\n"
            "  ∀ n : ℕ, 1 ≤ n → ∀ p : ℝ, 2 ≤ p →\n"
            "  ∀ v w : EuclideanSpace ℝ (Fin n),\n"
            "    (∀ i, 0 < v i) → (∀ i, 0 < w i) →\n"
            "      ‖epow p v‖ * ‖epow p w‖\n"
            "        - inner ℝ (epow p v) (epow p w)\n"
            "      ≤ ‖v‖ ^ p * ‖w‖ ^ p - (inner ℝ v w) ^ p\n"
            "\n"
            "theorem conjecture_5_1_true : Conjecture_5_1"
        )
        txt = Text(code, font=MONO, font_size=20, color=FG, line_spacing=0.8)
        box = SurroundingRectangle(txt, color=FAINT, fill_color="#121C2A", fill_opacity=1, buff=0.35, corner_radius=0.1)
        block = VGroup(box, txt).next_to(title, DOWN, buff=0.35)
        self.cap("Every step is also checked in Lean 4, a proof assistant, with the Mathlib library. This is the conjecture exactly as it is stated there.")
        self.play(FadeIn(box), AddTextLetterByLetter(txt, time_per_char=0.012))
        term = VGroup(
            Text("$ scripts/check.sh", font=MONO, font_size=20, color=MUTED),
            Text("no sorry, no extra axioms", font=MONO, font_size=20, color=GOOD),
            Text("axioms: propext, Classical.choice, Quot.sound", font=MONO, font_size=20, color=GOOD),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.1).next_to(block, DOWN, buff=0.25).align_to(block, LEFT)
        self.cap("The check script confirms there are no gaps and no extra assumptions. The equality cases and the weighted result are checked too.")
        for t in term:
            self.play(FadeIn(t, shift=RIGHT * 0.2), run_time=0.5)
        self.wait(2)
        self.clear(keep_caption=False)


# 11. What it is good for -------------------------------------------------------------------

E = np.array([0.0, 0.6, 1.1, 1.5, 2.4, 3.0])
F = np.array([1.2, 0.2, 0.9, 2.0, 0.5, 2.6])


def gibbs(energy, beta):
    weights = np.exp(-beta * energy)
    return weights / weights.sum()


class S11Applications(Base):
    def construct(self):
        title = label("What it is good for: cooling and sharpening", 34, GOLD, BOLD).to_edge(UP, buff=0.5)
        self.play(FadeIn(title))
        beta = ValueTracker(1.0)
        ax = Axes(x_range=[-0.5, 5.5, 1], y_range=[0, 0.8, 0.2], x_length=6.4, y_length=3.1, axis_config={"color": MUTED, "include_tip": False, "font_size": 20}, y_axis_config={"numbers_to_include": [0.2, 0.4, 0.6, 0.8]}).move_to(LEFT * 3.0 + UP * 0.1)

        def bars():
            P, Q = gibbs(E, beta.get_value()), gibbs(F, beta.get_value())
            g = VGroup()
            for i in range(6):
                for val, col, dx in ((P[i], VCOL, -0.17), (Q[i], WCOL, 0.17)):
                    bottom, top = ax.c2p(i + dx, 0), ax.c2p(i + dx, val)
                    g.add(Rectangle(width=0.3, height=max(0.001, top[1] - bottom[1]), fill_color=col, fill_opacity=0.9, stroke_width=0).move_to(bottom, aligned_edge=DOWN))
            return g

        b = always_redraw(bars)
        lab = always_redraw(lambda: MathTex(rf"\text{{inverse temperature }}\beta={beta.get_value():.2f}", font_size=28, color=GOLD).next_to(ax, UP, buff=0.2).align_to(ax, LEFT))
        bc = always_redraw(lambda: MathTex(rf"\text{{overlap BC}}={np.sum(np.sqrt(gibbs(E, beta.get_value()) * gibbs(F, beta.get_value()))):.3f}", font_size=28).next_to(ax, UP, buff=0.2).align_to(ax, RIGHT))
        self.cap("Take two probability distributions, for example a physical system with two different energy functions.")
        self.play(Create(ax), FadeIn(b), FadeIn(lab), FadeIn(bc))
        self.add(b, lab, bc)
        self.cap("Raising every probability to a power p and renormalising is the same as cooling the system by a factor p. The distributions sharpen and their overlap falls.")
        self.play(beta.animate.set_value(2.5), run_time=4)

        right = VGroup(
            MathTex(r"P\mapsto P^{(p)},\quad P^{(p)}_i=\frac{P_i^p}{\sum_j P_j^p}", font_size=32),
            MathTex(r"\sqrt{\textstyle\sum P_i^p\sum Q_i^p}\,\bigl(1-\mathrm{BC}(P^{(p)},Q^{(p)})\bigr)", font_size=30, color=VCOL),
            MathTex(r"\le\;1-\mathrm{BC}(P,Q)^p", font_size=30, color=WCOL),
        ).arrange(DOWN, buff=0.3).move_to(RIGHT * 3.6 + UP * 1.2)
        self.cap("Applied to the square roots of the probabilities, the theorem limits how much the overlap can fall, for every cooling factor of 2 or more.")
        self.play(Write(right), run_time=2.5)
        ml = label("Machine learning uses the same map.\nUDA sharpens predictions with\ntemperature 0.4, which is p = 2.5.", 26, FG).next_to(right, DOWN, buff=0.45)
        self.cap("Semi-supervised learning sharpens predictions in the same way. UDA uses temperature 0.4, which is p = 2.5, a case that needs the new theorem.")
        self.play(FadeIn(ml))
        self.play(beta.animate.set_value(1.0), run_time=2)
        self.wait(1)
        self.clear(keep_caption=False)


# 12. Outro -----------------------------------------------------------------------------------

class S12Outro(Base):
    def construct(self):
        recap = VGroup(
            label("Real powers p ≥ 2: proved", 30, GOOD),
            label("Every case of equality found", 30, GOOD),
            label("Weighted version characterised", 30, GOOD),
            label("All of it checked in Lean 4", 30, GOOD),
        ).arrange(DOWN, buff=0.3, aligned_edge=LEFT).shift(UP * 1.4)
        self.cap("So the conjecture is true, the threshold 2 comes from two by two matrices, and the whole argument is checked by computer.")
        for r in recap:
            self.play(FadeIn(r, shift=RIGHT * 0.3), run_time=0.5)
        links = VGroup(
            label("Lean proof: github.com/pragyaangaur/Real-Power-Cauchy-Schwarz", 22, MUTED),
            label("Principia Math, MathDB 369283", 22, MUTED),
            label("First informal proof: the automated system of Principia Math.", 20, MUTED),
            label("Pragyaan Gaur, 2026. Animated with Manim. Prepared with help from Claude.", 20, MUTED),
        ).arrange(DOWN, buff=0.18).next_to(recap, DOWN, buff=0.7)
        self.play(FadeIn(links))
        self.cap("Thank you for watching. The paper, the Lean code and an applications report are linked below.")
        self.wait(1)
        self.end_caption()
        self.play(*[FadeOut(m) for m in self.mobjects], run_time=1.2)
        self.caption = None


# Thumbnail ---------------------------------------------------------------------------------

class Thumbnail(Scene):
    def construct(self):
        title = label("Cauchy–Schwarz", 96, FG, BOLD)
        sub = label("for real powers", 72, GOLD, BOLD)
        formula = MathTex(
            r"\|v^p\|\,\|w^p\|-\langle v^p,w^p\rangle", r"\le", r"\|v\|^p\|w\|^p-\langle v,w\rangle^p", font_size=52
        )
        formula[0].set_color(VCOL)
        formula[2].set_color(WCOL)
        tag = label("CONJECTURE 5.1 · PROVED · CHECKED IN LEAN", 30, GOOD, BOLD)
        group = VGroup(title, sub, formula, tag).arrange(DOWN, buff=0.4)
        self.add(group)
