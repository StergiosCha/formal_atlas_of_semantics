# FORMAL ATLAS — visual identity briefs

Prompts for an image model (Gemini / Imagen / Nano Banana). Each is standalone —
paste one at a time. Ask for 4 variations, then iterate on the one you like by
appending a delta ("same, but the lambda counter is heavier").

The through-line: this is an **atlas**. Not a logic textbook cover, not a startup
mark. Cartography of theories — plates, legends, graticules, hand-drawn survey
lines — fused with the two symbols the field owns: the **λ** and the **turnstile ⊢**.
Proof General's signature is the *locked-proof region*: that amber/green shading
behind processed text. Steal it as the accent, not as a screenshot.

---

## 1. Primary logo (the mark)

> Design a minimalist vector logo for "Formal Atlas", a research tool that
> formalizes linguistic semantics theories in the Coq proof assistant.
>
> The mark: a lowercase Greek lambda (λ) whose two strokes are drawn as
> **meridian lines of a globe** — the descender curves like a longitude arc, so
> the letter reads simultaneously as a lambda and as a fragment of a map
> graticule. Behind it, three or four faint concentric latitude arcs, thin
> hairlines, suggesting a hemisphere without drawing a full circle.
>
> Style: precise geometric line art, single weight strokes, the restraint of a
> Swiss cartographic legend. Flat, no gradients, no bevels, no 3D.
> Colours: deep ink navy (#12203A) for the linework on warm paper white
> (#FAF7F0), with exactly one accent — an amber (#D98E20) highlight filling the
> wedge between the lambda's strokes, like the shaded "processed" region of a
> proof assistant.
>
> Deliver on a plain background, generous margin, no text, no tagline.
> Must survive being scaled to 24px: no detail finer than 1/20 of the height.

**Delta prompts to try after:**
- "…same, but replace the concentric arcs with a subtle turnstile ⊢ tucked into the negative space to the left of the lambda."
- "…same, but the lambda is formed by two crossing survey/triangulation lines with small tick marks, as on a geodetic map."

---

## 2. Wordmark / lockup

> A horizontal wordmark: the word "FORMAL ATLAS" set in a refined
> transitional serif (in the spirit of Times/Plantin as used on old survey
> plates), letter-spaced wide, small caps, deep ink navy. To its left, a square
> mark: a lowercase lambda drawn with meridian curvature, amber wedge accent.
> Between mark and text, a thin vertical hairline rule.
> Below the wordmark, in much smaller monospace letterspaced type:
> "SEMANTIC THEORIES, MACHINE-CHECKED".
> Flat vector, warm paper white background, no effects. Two versions: one
> light background, one on deep navy with the paper-white text inverted.

---

## 3. Hero visualization (the landing image)

This is the one that has to be beautiful. It renders the actual thing the
project produces: theories as plates, and *graded edges* between them.

> An elegant editorial data-visualization poster, in the visual language of a
> 19th-century scientific atlas plate reinterpreted with modern minimalism.
>
> Content: a network of about twelve labelled nodes floating on a warm
> paper-white field, connected by curved lines of varying weight and opacity.
> Each node is a small rectangular "plate" with a hairline border containing a
> tiny piece of mathematical notation — a lambda term, a turnstile sequent, a
> Sigma type, a pregroup reduction, a Bayesian ratio. The connecting curves are
> thin ink-navy arcs; some are solid and heavy, some are dashed and faint, as if
> the strength of each connection has been measured. A few arcs carry a small
> numeric label on a tiny amber tag.
>
> Behind everything: a very faint graticule of latitude/longitude hairlines and
> one or two ghosted contour-map shapes, at maybe 6% opacity, so the network
> reads as being surveyed onto a map.
>
> In the lower right, a small cartographic legend box, hairline border,
> explaining the line weights — the way a map legend explains elevation.
>
> Palette: warm paper white #FAF7F0, deep ink navy #12203A, one amber accent
> #D98E20, and a single muted sage #6E8B74 used sparingly for the faintest arcs.
> No neon, no glow, no dark-mode tech aesthetic, no circuit boards, no brains,
> no robots.
>
> Composition: generous white space, asymmetric, the network occupying the upper
> two-thirds. 16:9. Print-quality line crispness.

**Delta prompts:**
- "…same composition, but the background ghost shape is a topographic contour map whose contour lines follow the density of the network."
- "…same, but render it as a two-colour risograph print, navy and amber only, with slight registration offset."
- "…dark variant: deep navy field, paper-white linework, amber accent unchanged."

---

## 4. Section / theory-page headers

Small repeatable illustrations, one per region of the atlas. Same prompt,
swap the bracketed content:

> A small square emblem in the style of a cartographic map symbol: hairline
> vector linework, deep ink navy on warm paper white, one amber accent detail,
> flat, no shading, generous margin. The emblem depicts [MOTIF]. Minimal —
> at most a dozen strokes. It should read as a legend symbol on a map, not as
> an illustration.

| Region | `[MOTIF]` |
|---|---|
| Montague | a rising staircase of nested brackets resolving into a single lambda |
| Type-logical | a Lambek slash `/` and backslash `\` interlocking like a surveyor's cross |
| Modern type theory | nested Sigma shapes stacked as a telescope narrowing to a point |
| Dynamic | two boxes joined by an arrow that loops back, DRT-box style |
| Inquisitive | overlapping information states drawn as soft intersecting lens shapes |
| Probabilistic | a small histogram whose bars are proportioned 3:1 |
| Categorical | a compact-closed "snake" — a wire bending back through two cups |

---

## 5. Favicon

> A 64×64 app icon: a single lowercase lambda with meridian curvature, deep ink
> navy, on a warm paper-white rounded square, with an amber wedge filling the
> space between the lambda's legs. Extremely simple, no text, legible at 16px.

---

## Palette (use these verbatim in CSS)

```
--paper:  #FAF7F0   /* warm paper white — page background */
--ink:    #12203A   /* deep navy — text and linework */
--amber:  #D98E20   /* the "proof locked" accent, Proof General's shading */
--sage:   #6E8B74   /* muted green — QED, verified badges */
--rust:   #A64B3A   /* refuted / countermodel */
--fog:    #E7E1D6   /* hairlines, table rules */
```

Type pairing: a transitional serif for headings and prose (survey-plate
feeling), a monospace with real Greek and math glyphs for Coq source and
inline notation — **JuliaMono**, **Iosevka** or **DejaVu Sans Mono** all cover
λ, ⊢, Σ, Π, ⊨ without falling back mid-line, which is the usual thing that
makes a semantics site look cheap.
