from pptx import Presentation
from pptx.util import Inches, Pt, Emu
from pptx.dml.color import RGBColor
from pptx.enum.text import PP_ALIGN
from pptx.util import Inches, Pt
import pptx.oxml.ns as nsmap
from lxml import etree
import copy

# ── Palette ──────────────────────────────────────────────
BG_DARK   = RGBColor(0x0a, 0x0a, 0x0f)
BG_CARD   = RGBColor(0x12, 0x12, 0x1e)
ACCENT    = RGBColor(0x6b, 0x7a, 0xff)
ACCENT2   = RGBColor(0xa7, 0x8b, 0xfa)
WHITE     = RGBColor(0xff, 0xff, 0xff)
GRAY      = RGBColor(0x88, 0x92, 0xb0)
LGRAY     = RGBColor(0xb0, 0xbe, 0xc5)
CARD_BDR  = RGBColor(0x2a, 0x2a, 0x40)

SLIDE_W = Inches(13.33)
SLIDE_H = Inches(7.5)

prs = Presentation()
prs.slide_width  = SLIDE_W
prs.slide_height = SLIDE_H

blank_layout = prs.slide_layouts[6]   # completely blank


# ── Helpers ──────────────────────────────────────────────

def add_rect(slide, x, y, w, h, fill=None, line=None, line_w=None):
    shape = slide.shapes.add_shape(1, x, y, w, h)   # MSO_SHAPE_TYPE.RECTANGLE = 1
    shape.line.fill.background()
    if fill:
        shape.fill.solid()
        shape.fill.fore_color.rgb = fill
    else:
        shape.fill.background()
    if line:
        shape.line.color.rgb = line
        if line_w:
            shape.line.width = line_w
    else:
        shape.line.fill.background()
    return shape


def add_text(slide, text, x, y, w, h,
             size=18, bold=False, color=WHITE, align=PP_ALIGN.LEFT,
             wrap=True, italic=False):
    txb = slide.shapes.add_textbox(x, y, w, h)
    tf  = txb.text_frame
    tf.word_wrap = wrap
    p   = tf.paragraphs[0]
    p.alignment = align
    run = p.add_run()
    run.text = text
    run.font.size  = Pt(size)
    run.font.bold  = bold
    run.font.color.rgb = color
    run.font.italic = italic
    return txb


def bg(slide):
    """Fill slide background dark."""
    add_rect(slide, 0, 0, SLIDE_W, SLIDE_H, fill=BG_DARK)


def label(slide, text):
    """Small accent label at the top-left."""
    add_text(slide, text.upper(),
             Inches(0.7), Inches(0.35), Inches(6), Inches(0.35),
             size=9, bold=True, color=ACCENT)


def title_text(slide, text, y=Inches(0.85), size=40):
    txb = slide.shapes.add_textbox(Inches(0.7), y, Inches(11.9), Inches(1.4))
    tf  = txb.text_frame
    tf.word_wrap = True
    p   = tf.paragraphs[0]
    p.alignment = PP_ALIGN.LEFT
    run = p.add_run()
    run.text = text
    run.font.size  = Pt(size)
    run.font.bold  = True
    run.font.color.rgb = WHITE


def card(slide, x, y, w, h, icon, heading, body):
    add_rect(slide, x, y, w, h, fill=BG_CARD, line=CARD_BDR, line_w=Pt(0.75))
    add_text(slide, icon,    x+Inches(0.2), y+Inches(0.15), Inches(0.5), Inches(0.45), size=20)
    add_text(slide, heading, x+Inches(0.2), y+Inches(0.55), w-Inches(0.4), Inches(0.35),
             size=12, bold=True, color=RGBColor(0xc5, 0xce, 0xff))
    add_text(slide, body,    x+Inches(0.2), y+Inches(0.88), w-Inches(0.4), h-Inches(1.0),
             size=10, color=GRAY, wrap=True)


def timeline_item(slide, year, heading, body, y):
    # year
    add_text(slide, year, Inches(0.7), y, Inches(0.9), Inches(0.3),
             size=10, bold=True, color=ACCENT, align=PP_ALIGN.RIGHT)
    # dot
    dot = add_rect(slide, Inches(1.72), y+Inches(0.08), Inches(0.14), Inches(0.14),
                   fill=ACCENT)
    dot.line.fill.background()
    # heading
    add_text(slide, heading, Inches(2.0), y, Inches(9.5), Inches(0.28),
             size=11, bold=True, color=RGBColor(0xc5, 0xce, 0xff))
    # body
    add_text(slide, body, Inches(2.0), y+Inches(0.3), Inches(9.5), Inches(0.35),
             size=10, color=GRAY, wrap=True)


def bullet(slide, text, y, indent=False):
    x = Inches(1.1) if indent else Inches(0.9)
    add_text(slide, "▸  " + text, x, y, Inches(11.3), Inches(0.45),
             size=11, color=LGRAY, wrap=True)


def quote_box(slide, text, y=Inches(1.9)):
    add_rect(slide, Inches(0.7), y, Inches(11.9), Inches(1.2),
             fill=RGBColor(0x10, 0x10, 0x25), line=ACCENT, line_w=Pt(1))
    add_text(slide, text, Inches(1.0), y+Inches(0.15), Inches(11.3), Inches(0.9),
             size=13, color=RGBColor(0xc5, 0xce, 0xff), italic=True, wrap=True)


# ═══════════════════════════════════════════════════════════
# SLIDE 1 — Cover
# ═══════════════════════════════════════════════════════════
sl = prs.slides.add_slide(blank_layout)
bg(sl)

# Decorative circles (just rectangles with rounded corners would need XML;
# use thin-border rectangles as decorative accents instead)
add_rect(sl, Inches(9.5), Inches(-0.5), Inches(5), Inches(5),
         fill=None, line=RGBColor(0x1a, 0x1a, 0x35), line_w=Pt(0.5))
add_rect(sl, Inches(-0.3), Inches(5.2), Inches(3), Inches(3),
         fill=None, line=RGBColor(0x1a, 0x1a, 0x35), line_w=Pt(0.5))

label(sl, "Emerging AI Research")

# Main title
add_text(sl, "AI World Models", Inches(0.7), Inches(1.2), Inches(10), Inches(1.3),
         size=54, bold=True, color=WHITE)
add_text(sl, "Evolution", Inches(0.7), Inches(2.4), Inches(10), Inches(1.0),
         size=54, bold=True, color=ACCENT)

add_text(sl,
    "From reactive pattern matching to internal simulations of reality —\n"
    "how machines are learning to understand the world.",
    Inches(0.7), Inches(3.6), Inches(9), Inches(1.0),
    size=14, color=GRAY, wrap=True)

# Tags
tags = ["World Models", "Deep Learning", "Reinforcement Learning",
        "Foundation Models", "AGI Research"]
tx = Inches(0.7)
for t in tags:
    tb = add_text(sl, f"  {t}  ", tx, Inches(4.9), Inches(2.2), Inches(0.38),
                  size=9, color=ACCENT, align=PP_ALIGN.CENTER)
    add_rect(sl, tx, Inches(4.9), Inches(len(t)*0.085 + 0.25), Inches(0.35),
             fill=RGBColor(0x10, 0x10, 0x25), line=ACCENT, line_w=Pt(0.75))
    add_text(sl, t, tx+Inches(0.05), Inches(4.93), Inches(len(t)*0.085+0.15), Inches(0.3),
             size=9, color=ACCENT)
    tx += Inches(len(t)*0.085 + 0.35)

add_text(sl, "April 2026", Inches(0.7), Inches(6.9), Inches(4), Inches(0.35),
         size=10, color=RGBColor(0x40, 0x45, 0x60))


# ═══════════════════════════════════════════════════════════
# SLIDE 2 — What Is a World Model?
# ═══════════════════════════════════════════════════════════
sl = prs.slides.add_slide(blank_layout)
bg(sl)
label(sl, "Foundations")
title_text(sl, "What Is a World Model?")

quote_box(sl,
    '"A world model is an internal representation that an agent uses to simulate, '
    'predict, and reason about its environment — enabling planning beyond immediate perception."',
    y=Inches(1.85))

items = [
    ("🧠", "Internal Representation",
     "A compressed, structured model of how the world looks, works, and changes over time."),
    ("🔮", "Predictive Engine",
     "Enables the agent to simulate future states and evaluate potential actions before committing."),
    ("🗺️", "Planning Foundation",
     "Decouples perception from action, allowing abstract, long-horizon reasoning and goal-seeking."),
]
cw = Inches(3.8)
cx = Inches(0.7)
for icon, h, b in items:
    card(sl, cx, Inches(3.25), cw, Inches(3.0), icon, h, b)
    cx += cw + Inches(0.25)


# ═══════════════════════════════════════════════════════════
# SLIDE 3 — Early Roots
# ═══════════════════════════════════════════════════════════
sl = prs.slides.add_slide(blank_layout)
bg(sl)
label(sl, "Era 1 · 1980s – 2000s")
title_text(sl, "Early Roots: Symbolic & Probabilistic")

# vertical line
add_rect(sl, Inches(1.75), Inches(1.85), Inches(0.03), Inches(5.1),
         fill=RGBColor(0x2a, 0x2a, 0x50))

rows = [
    ("1986", "Rumelhart's Mental Models",
     "Connectionist approaches suggest distributed representations as a substrate for world knowledge."),
    ("1989", "Dyna Architecture (Sutton)",
     "First formal RL framework integrating a learned environment model for simulated planning."),
    ("1998", "POMDP & Belief States",
     "Partially Observable MDPs introduce probability distributions over hidden world states."),
    ("2001", "Kalman Filter Robotics",
     "Mobile robots maintain probabilistic maps — early practical world models for navigation."),
]
y = Inches(1.85)
for year, h, b in rows:
    timeline_item(sl, year, h, b, y)
    y += Inches(1.3)


# ═══════════════════════════════════════════════════════════
# SLIDE 4 — Deep Learning Era
# ═══════════════════════════════════════════════════════════
sl = prs.slides.add_slide(blank_layout)
bg(sl)
label(sl, "Era 2 · 2012 – 2018")
title_text(sl, "Deep Learning Era")

items = [
    ("🕹️", "DQN & Atari (DeepMind, 2013)",
     "Deep Q-Networks learn reactive policies directly from pixels — latent representations begin capturing game dynamics."),
    ("🌀", "Variational Autoencoders (2013)",
     "VAEs learn compact, continuous latent spaces — a structural precursor to learned world state representations."),
    ("📽️", "Video Prediction Models (2015–17)",
     "Models like PredNet and Action-Conditioned Video Prediction learn to simulate environment frames forward in time."),
    ("🤖", "World Models Paper (Ha & Schmidhuber, 2018)",
     "Landmark work: a VAE + MDN-RNN model allows an agent to train entirely inside its own dream of the environment."),
]
cw = Inches(5.9)
cy = Inches(1.85)
for i, (icon, h, b) in enumerate(items):
    cx = Inches(0.7) if i % 2 == 0 else Inches(6.85)
    row = i // 2
    card(sl, cx, cy + row * Inches(2.65), cw, Inches(2.45), icon, h, b)


# ═══════════════════════════════════════════════════════════
# SLIDE 5 — World Models 2018 Breakdown
# ═══════════════════════════════════════════════════════════
sl = prs.slides.add_slide(blank_layout)
bg(sl)
label(sl, "Milestone")
title_text(sl, 'Ha & Schmidhuber — "World Models" (2018)')

add_text(sl,
    "Three-component architecture that became the canonical blueprint for learned world models:",
    Inches(0.7), Inches(1.75), Inches(11.9), Inches(0.4),
    size=12, color=LGRAY, wrap=True)

items = [
    ("👁️", "V — Visual Model",
     'A VAE compresses each frame into a small latent vector z, capturing essential visual structure.'),
    ("💭", "M — Memory (MDN-RNN)",
     "A recurrent network predicts the future latent state distribution, modeling temporal dynamics."),
    ("🎮", "C — Controller",
     "A compact linear model maps (z, h) → action. The agent can train entirely in the dream world."),
]
cw = Inches(3.8)
cx = Inches(0.7)
for icon, h, b in items:
    card(sl, cx, Inches(2.3), cw, Inches(2.8), icon, h, b)
    cx += cw + Inches(0.25)

# Stats
stats = [("1st", "Agent trained in dream"), ("900+", "Citations"), ("3", "Modular components")]
sx = Inches(0.7)
for val, lbl in stats:
    add_text(sl, val, sx, Inches(5.4), Inches(3.5), Inches(0.75),
             size=34, bold=True, color=ACCENT)
    add_text(sl, lbl.upper(), sx, Inches(6.1), Inches(3.5), Inches(0.4),
             size=9, color=RGBColor(0x40, 0x45, 0x60))
    sx += Inches(4.0)


# ═══════════════════════════════════════════════════════════
# SLIDE 6 — Dreamer
# ═══════════════════════════════════════════════════════════
sl = prs.slides.add_slide(blank_layout)
bg(sl)
label(sl, "Era 3 · 2019 – 2021")
title_text(sl, "Latent Imagination & Dreamer")

add_text(sl,
    "DeepMind's Dreamer series unified model learning and policy optimization entirely inside a learned latent space, achieving state-of-the-art sample efficiency.",
    Inches(0.7), Inches(1.75), Inches(11.9), Inches(0.6),
    size=12, color=LGRAY, wrap=True)

items = [
    ("💡", "DreamerV1 (2019)",
     "RSSM latent model + value/actor trained on imagined rollouts. Beats model-free baselines on 20 Atari games with 5× less data."),
    ("🚀", "DreamerV2 (2020)",
     "Discrete latent representations (categorical VAE) dramatically improve stability. Matches human-level Atari performance."),
    ("🌍", "DreamerV3 (2023)",
     "Single hyperparameter set across domains: Atari, continuous control, Minecraft diamond collection — a true general world model agent."),
]
cw = Inches(3.8)
cx = Inches(0.7)
for icon, h, b in items:
    card(sl, cx, Inches(2.6), cw, Inches(3.6), icon, h, b)
    cx += cw + Inches(0.25)


# ═══════════════════════════════════════════════════════════
# SLIDE 7 — LLMs as World Models
# ═══════════════════════════════════════════════════════════
sl = prs.slides.add_slide(blank_layout)
bg(sl)
label(sl, "Era 4 · 2020 – 2023")
title_text(sl, "Language Models as World Models")

add_text(sl,
    "LLMs trained on internet-scale text encode rich implicit world knowledge — effectively learning a probabilistic world model through next-token prediction.",
    Inches(0.7), Inches(1.75), Inches(11.9), Inches(0.55),
    size=12, color=LGRAY, wrap=True)

bullets = [
    "GPT-3 (2020): Demonstrates emergent world knowledge, causal reasoning, and physical intuition from text alone.",
    "DALL-E & Imagen (2021–22): Multimodal models learn visual world structure from image–caption pairs at scale.",
    '"Language Models are Zero-Shot Reasoners" (2022): Chain-of-thought prompting reveals latent step-by-step simulation.',
    "GPT-4 / Claude 2 (2023): Models pass professional exams and solve physics problems — deep world model internalization.",
    "Sparks of AGI (Microsoft, 2023): Argues GPT-4 exhibits rudimentary theory of mind and causal world understanding.",
]
y = Inches(2.55)
for b in bullets:
    bullet(sl, b, y)
    y += Inches(0.83)


# ═══════════════════════════════════════════════════════════
# SLIDE 8 — Multimodal & Embodied
# ═══════════════════════════════════════════════════════════
sl = prs.slides.add_slide(blank_layout)
bg(sl)
label(sl, "Era 5 · 2023 – 2024")
title_text(sl, "Multimodal & Embodied World Models")

items = [
    ("🦾", "RT-2 / RT-X (Google, 2023)",
     "Vision-language-action model that transfers internet world knowledge to robotic manipulation."),
    ("🎬", "Sora (OpenAI, 2024)",
     "Diffusion transformer trained on video generates physically plausible scenes with deep implicit 3D dynamics."),
    ("🗺️", "Genie (DeepMind, 2024)",
     "Learns an interactive world model from unlabeled video — generates playable 2D environments from a single image."),
    ("🧩", "V-JEPA (Meta, 2024)",
     "Joint Embedding Predictive Architecture learns abstract world representations by predicting in latent space."),
]
cw = Inches(5.9)
cy = Inches(1.85)
for i, (icon, h, b) in enumerate(items):
    cx = Inches(0.7) if i % 2 == 0 else Inches(6.85)
    row = i // 2
    card(sl, cx, cy + row * Inches(2.65), cw, Inches(2.45), icon, h, b)


# ═══════════════════════════════════════════════════════════
# SLIDE 9 — Architectural Comparison Table
# ═══════════════════════════════════════════════════════════
sl = prs.slides.add_slide(blank_layout)
bg(sl)
label(sl, "Technical Deep Dive")
title_text(sl, "Architectural Generations")

headers = ["Generation", "State Space", "Learning Signal", "Planning", "Key Limitation"]
rows_data = [
    ["Symbolic / Kalman", "Gaussian belief", "Hand-crafted", "Linear-Gaussian", "No learning from data"],
    ["VAE + MDN-RNN",     "Continuous latent z", "Reconstruction", "CMA-ES in dream", "Poor long-horizon fidelity"],
    ["RSSM (Dreamer)",    "Stochastic + det.", "ELBO + reward", "Latent imagination", "Compounding dream errors"],
    ["LLM-based",         "Token sequences", "Next-token pred.", "CoT / search", "No persistent state"],
    ["Video diffusion",   "Pixel / latent video", "Denoising score", "Implicit rollout", "Slow, not interactive"],
    ["JEPA / Abstract",   "Abstract embeddings", "Predictive SSL", "Latent search", "Early-stage research"],
]

col_w = [Inches(2.1), Inches(1.9), Inches(1.9), Inches(1.9), Inches(2.4)]
col_x = [Inches(0.55)]
for w in col_w[:-1]:
    col_x.append(col_x[-1] + w + Inches(0.05))

# Header row
hy = Inches(1.85)
for i, (h, x, w) in enumerate(zip(headers, col_x, col_w)):
    add_rect(sl, x, hy, w, Inches(0.38), fill=RGBColor(0x10, 0x10, 0x28),
             line=CARD_BDR, line_w=Pt(0.5))
    add_text(sl, h, x+Inches(0.1), hy+Inches(0.05), w-Inches(0.1), Inches(0.3),
             size=9, bold=True, color=ACCENT, align=PP_ALIGN.LEFT)

row_h = Inches(0.73)
for ri, row in enumerate(rows_data):
    ry = Inches(2.28) + ri * row_h
    bg_c = RGBColor(0x0e, 0x0e, 0x1a) if ri % 2 == 0 else RGBColor(0x12, 0x12, 0x20)
    for ci, (cell, x, w) in enumerate(zip(row, col_x, col_w)):
        add_rect(sl, x, ry, w, row_h-Inches(0.04), fill=bg_c,
                 line=CARD_BDR, line_w=Pt(0.3))
        color = RGBColor(0xc5, 0xce, 0xff) if ci == 0 else GRAY
        add_text(sl, cell, x+Inches(0.1), ry+Inches(0.1), w-Inches(0.15), row_h-Inches(0.15),
                 size=9, bold=(ci == 0), color=color, wrap=True)


# ═══════════════════════════════════════════════════════════
# SLIDE 10 — Open Challenges
# ═══════════════════════════════════════════════════════════
sl = prs.slides.add_slide(blank_layout)
bg(sl)
label(sl, "Current Frontier")
title_text(sl, "Open Challenges")

challenges = [
    ("⏳", "Long-Horizon Fidelity",    "Errors accumulate in dream rollouts; models fail beyond a few dozen steps."),
    ("🔄", "Persistent State",         "LLMs lack a continuously updated world state — each context window is stateless."),
    ("🌐", "Grounding & Causality",    "Models learn correlations; distinguishing causal mechanisms from confounders remains unsolved."),
    ("📐", "Compositionality",         "Combining learned concepts in novel configurations — systematic generalization — is still brittle."),
    ("🏃", "Real-Time Inference",      "Video and diffusion world models are too slow for interactive robotics and real-time planning."),
    ("🎯", "Reward Specification",     "World models trained without reward signals may not represent dimensions relevant to goals."),
    ("🔒", "Safety & Alignment",       "An agent with a powerful world model can reason about manipulating its environment — raising stakes."),
    ("🧪", "Evaluation",               "No standard benchmark captures whether a model truly understands vs. pattern-matches world states."),
]

cw = Inches(2.85)
ch = Inches(2.0)
for i, (icon, h, b) in enumerate(challenges):
    col = i % 4
    row = i // 4
    cx = Inches(0.55) + col * (cw + Inches(0.18))
    cy = Inches(1.75) + row * (ch + Inches(0.18))
    card(sl, cx, cy, cw, ch, icon, h, b)


# ═══════════════════════════════════════════════════════════
# SLIDE 11 — Future Directions
# ═══════════════════════════════════════════════════════════
sl = prs.slides.add_slide(blank_layout)
bg(sl)
label(sl, "Looking Forward")
title_text(sl, "The Road Ahead")

items = [
    ("🧬", "Unified Architectures",
     "Converging language, perception, and action into a single world model backbone (e.g., JEPA variants, multimodal RSSM)."),
    ("🌱", "Continuous Learning",
     "Models that update their world model online from new experience without catastrophic forgetting."),
    ("🤝", "Theory of Mind",
     "Explicitly modeling other agents' beliefs and intentions within the world model for social and cooperative AI."),
]
cw = Inches(3.8)
cx = Inches(0.7)
for icon, h, b in items:
    card(sl, cx, Inches(1.85), cw, Inches(2.6), icon, h, b)
    cx += cw + Inches(0.25)

quote_box(sl,
    '"The next leap in AI capability will likely come not from larger models, but from models that '
    'build and maintain richer, more accurate internal simulations of how the world actually works."',
    y=Inches(4.65))

# Tags
tags2 = ["Neuro-symbolic hybrids", "Causal world models", "Embodied AGI",
         "Self-supervised grounding", "Predictive coding"]
tx = Inches(0.7)
ty = Inches(6.1)
for t in tags2:
    w = Inches(len(t) * 0.087 + 0.3)
    add_rect(sl, tx, ty, w, Inches(0.3), fill=RGBColor(0x10, 0x10, 0x25),
             line=ACCENT, line_w=Pt(0.75))
    add_text(sl, t, tx+Inches(0.07), ty+Inches(0.03), w, Inches(0.27),
             size=8, color=ACCENT)
    tx += w + Inches(0.15)


# ── Save ─────────────────────────────────────────────────
out = "/home/user/claude/ai_world_models.pptx"
prs.save(out)
print(f"Saved → {out}")
