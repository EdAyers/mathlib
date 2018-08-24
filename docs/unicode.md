A list of commonly used symbols in Lean. 
I reccomend using this document by copy and pasting the symbol you want into a `.lean` file in vscode and then hovering over the symbol to see the completion string for it. 
I've taken the unicode charts and pruned out the pointless characters that nobody uses.
I am using the font [PragmataPro](https://www.fsd.it/shop/fonts/pragmatapro/?attribute_weights=PragmataPro+Regular+with+PP+Mono+Regular&attribute_license-for=desktop). 
In which all of the below symbols are rendered nicely and distinguishably.
I like PragmataPro because it keeps to the letter grid even with the more obscure symbols.
## Letters
```
 A B C D E F G H I J K L M N O P Q R S T U V W X Y Z
 a b c d e f g h i j k l m n o p q r s t u v w x y z
 0 1 2 3 4 5 6 7 8 9
```
### Greek
I've removed the letters which clash with latin letters.
```
 Γ Δ Θ Λ Ξ Π Σ Υ Φ Ψ Ω
 α β γ δ ε ζ η θ ι κ λ μ ν ξ π ρ ς σ τ υ φ χ ψ ω 
 ∂   ϑ ϰ ϕ ϱ ϖ
```
## Letter-like mathematical symbols in unicode.
The unicode standard messes up how it codes mathematical symbols. This is because there are two charts:
- [Letterlike Symbols](http://www.unicode.org/charts/PDF/U2100.pdf) `U+2100-214F`
- [Mathematical Alphanumeric Symbols](http://www.unicode.org/charts/PDF/U1D400.pdf) `U+1D400–1D7FF`
Some characters such as what we would write as `\mathbb{R}` in LaTeX, appear in both of these charts. Both `U+211D` (`ℝ`) and `U+1D549` (`𝕉`) look like the symbol we use for the reals but are actually distinct unicode characters and so Lean will treat them differently. The actual unicode chart says `U+1D549` is blank but many fonts render it to look like the `U+211D`. I think the convention is to use the `U+2100-214F` chart unless it doesn't have your character, and then use the `U+1D400–1D7FF` chart.
### The 'letterlike symbols`
```
U+2100  ℀ ℁ ℂ ℃ ℄ ℅ ℆ ℇ ℈ ℉ ℊ ℋ ℌ ℍ ℎ ℏ
U+2110  ℐ ℑ ℒ ℓ ℔ ℕ № ℗ ℘ ℙ ℚ ℛ ℜ ℝ ℞ ℟
U+2120  ℠ ℡ ™ ℣ ℤ ℥ Ω ℧ ℨ ℩ K Å ℬ ℭ ℮ ℯ
U+2130  ℰ ℱ Ⅎ ℳ ℴ ℵ ℶ ℷ ℸ ℹ ℺ ℻ ℼ ℽ ℾ ℿ
U+2140  ⅀ ⅁ ⅂ ⅃ ⅄ ⅅ ⅆ ⅇ ⅈ ⅉ ⅊ ⅋ ⅌ ⅍ ⅎ ⅏
```
## Chart __1D400–1D7FF__
All of the following characters are exclusively in the `U+1D400–1D7FF` chart. I have ommitted the characters that don't look good in my font (PragmataPro). You should resist using these characters as they can make things confusing.
### Mathematical Bold
[WARNING] These are not in Lean yet.
```
 𝐀 𝐁 𝐂 𝐃 𝐄 𝐅 𝐆 𝐇 𝐈 𝐉 𝐊 𝐋 𝐌 𝐍 𝐎 𝐏 𝐐 𝐑 𝐒 𝐓 𝐔 𝐕 𝐖 𝐗 𝐘 𝐙 
 𝐚 𝐛 𝐜 𝐝 𝐞 𝐟 𝐠 𝐡 𝐢 𝐣 𝐤 𝐥 𝐦 𝐧 𝐨 𝐩 𝐪 𝐫 𝐬 𝐭 𝐮 𝐯 𝐰 𝐱 𝐲 𝐳 
 𝟎 𝟏 𝟐 𝟑 𝟒 𝟓 𝟔 𝟕 𝟖 𝟗 
```
### Mathematical Italic
[WARNING] These are not in Lean yet.
```
 𝐴 𝐵 𝐶 𝐷 𝐸 𝐹 𝐺 𝐻 𝐼 𝐽 𝐾 𝐿 𝑀 𝑁 𝑂 𝑃 𝑄 𝑅 𝑆 𝑇 𝑈 𝑉 𝑊 𝑋 𝑌 𝑍 
 𝑎 𝑏 𝑐 𝑑 𝑒 𝑓 𝑔 𝑕 𝑖 𝑗 𝑘 𝑙 𝑚 𝑛 𝑜 𝑝 𝑞 𝑟 𝑠 𝑡 𝑢 𝑣 𝑤 𝑥 𝑦 𝑧 
 𝛤 𝛥 𝛩 𝛬 𝛯 𝛱 𝛳 𝛴 𝛶 𝛷 𝛸 𝛹 𝛺 𝛻 
 𝛼 𝛽 𝛾 𝛿 𝜀 𝜁 𝜂 𝜃 𝜄 𝜅 𝜆 𝜇 𝜈 𝜉 𝜋 𝜌 𝜍 𝜎 𝜏 𝜐 𝜑 𝜒 𝜓 𝜔 
 𝜕 𝜖 𝜗 𝜘 𝜙 𝜚 𝜛 
```

### Mathematical Script
Type with `\McX`
```
 𝒜 𝒝 𝒞 𝒟 𝒠 𝒡 𝒢 𝒣 𝒤 𝒥 𝒦 𝒧 𝒨 𝒩 𝒪 𝒫 𝒬 𝒭 𝒮 𝒯 𝒰 𝒱 𝒲 𝒳 𝒴 𝒵 
 𝒶 𝒷 𝒸 𝒹 𝒺 𝒻 𝒼 𝒽 𝒾 𝒿 𝓀 𝓁 𝓂 𝓃 𝓄 𝓅 𝓆 𝓇 𝓈 𝓉 𝓊 𝓋 𝓌 𝓍 𝓎 𝓏 
```
I am omitting _Mathematical Bold Script_ because it looks too similar.
### Mathematical Fraktur
Type with `\MfX`
```
 𝔄 𝔅 𝔆 𝔇 𝔈 𝔉 𝔊 𝔋 𝔌 𝔍 𝔎 𝔏 𝔐 𝔑 𝔒 𝔓 𝔔 𝔕 𝔖 𝔗 𝔘 𝔙 𝔚 𝔛 𝔜 𝔝 
 𝔞 𝔟 𝔠 𝔡 𝔢 𝔣 𝔤 𝔥 𝔦 𝔧 𝔨 𝔩 𝔪 𝔫 𝔬 𝔭 𝔮 𝔯 𝔰 𝔱 𝔲 𝔳 𝔴 𝔵 𝔶 𝔷 
```
I am omitting _Mathematical Bold Fraktur_ because it looks too similar.
### Mathematical Double-Struck
Type with `\bbX`.
```
 𝔸 𝔹 𝔺 𝔻 𝔼 𝔽 𝔾 𝔿 𝕀 𝕁 𝕂 𝕃 𝕄 𝕅 𝕆 𝕇 𝕈 𝕉 𝕊 𝕋 𝕌 𝕍 𝕎 𝕏 𝕐 𝕑 
 𝕒 𝕓 𝕔 𝕕 𝕖 𝕗 𝕘 𝕙 𝕚 𝕛 𝕜 𝕝 𝕞 𝕟 𝕠 𝕡 𝕢 𝕣 𝕤 𝕥 𝕦 𝕧 𝕨 𝕩 𝕪 𝕫 
 𝟘 𝟙 𝟚 𝟛 𝟜 𝟝 𝟞 𝟟 𝟠 𝟡
```

I have removed Mathematical Monospace and Sans-Serif because in Pragmata Pro the glyphs are identical to the ASCII letters.

## Accents and so on.

I am mostly against decorating letters with accents so I am not in a rush to fill out this section. There are also many Unicode caveats. For example:

- `ë` is `U+00EB` (Latin)
- `ё` is `U+0450` (Cyrillic)
- `e̎` is `U+0065 U+0308` and uses a [combining diaresis](https://www.unicode.org/charts/PDF/U0300.pdf). Sometimes the combining marks look nice and sometimes the font butchers them.

It's an absolute minefield.

## Subscripts and superscripts

```
² ³
U+2070  ⁰ ⁱ   ⁴ ⁵ ⁶ ⁷ ⁸ ⁹ ⁺ ⁻ ⁼ ⁽ ⁾ ⁿ
U+2080  ₀ ₁ ₂ ₃ ₄ ₅ ₆ ₇ ₈ ₉ ₊ ₋ ₌ ₍ ₎
U+2090  ₐ ₑ ₒ ₓ ₔ ₕ ₖ ₗ ₘ ₙ ₚ ₛ ₜ
```

## Brackets
```
( ) [ ] { }
⦃ ⦄ ⟦ ⟧ ⟨ ⟩ ⟪ ⟫ 
‹ › « » 
⁅ ⁆ ⌈ ⌉ ⌊ ⌋ ⌜ ⌝ ⌞ ⌟
```
These don't have completions:
```
⟮ ⟯ ⟬ ⟭   
⦋ ⦌ ⦍ ⦎ ⦏ ⦐
⦉ ⦊ ⦅ ⦆ ⦇ ⦈ ⨴ ⨵
```

## Symbols
```
∀ ∂ ∃ ∄ ∅ ∝ ∞ √ ∛ ∜ ∫ ∮ ∱ ∲ ∳ ∓ ± ∆ ∇
```
### big ops
```
⋀ ⋁ ⋂ ⋃ ⨅ ⨆ ∏ ∐ ∑ ⨁ ⨂ ⨀ 
```
### products 
```
∗ ∘ ∙ ⋄ ⋅ ⋆ ⋇ ⋈ ※
⊍ ⊎ 
⊕ ⊖ ⊗ ⊘ ⊙ ⊚ ⊛ ⊜ ⊝ 
⊞ ⊟ ⊠ ⊡ 
∴ ∵ ⁖ ⋮ ⋯ ⁘ ⁙
```


### relations
```
< > ≤ ≥ ≮ ≯ ≰ ≱ ∧ ∨
≺ ≻ ≼ ≽ ⊀ ⊁     ⋏ ⋎
⊂ ⊃ ⊆ ⊇ ⊄ ⊅ ⊈ ⊉ ∩ ∪
∈ ∋     ∉ ∌
⊲ ⊳ ⊴ ⊵         
⊏ ⊐ ⊑ ⊒         ⊓ ⊔ 
⋐⋑            ⋒⋓

≃ ≄ ≅ ≇ ≈ ≉ ≊ ≋ ≍ ≎ ≏ ≐ ≑ ≒ ≓
≖ ≗ ≘ ≙ ≚ ≛ ≜ ≝ ≞ ≟ ≠ ≡ ≢ ≣
≪ ≫ ⋘ ⋙
⊢ ⊣ ⊤ ⊥ ⊦ ⊧ ⊨ ⊩ ⊪ ⊫
```
## arrows
```
← ↑ → ↓ ↔ ↕ ⟵ ⟶ ⟷
⇐ ⇑ ⇒ ⇓ ⇔ ⇕ ⟸ ⟹ ⟺
↤ ↥ ↦ ↧      ⟻ ⟼
⇜   ⇝   ↭   ⬳ ⟿ 
↞ ↟ ↠ ↡ 
↜   ↝ 
↢   ↣ 
⇇ ⇈ ⇉ ⇊ 
⇚ ⟰ ⇛ ⟱

↫ ↬ ↩ ↪ ↯ ↺ ↻ ⇶
```
### arrows with evil twins
I stipulate using these:
```
↼ ↾ ⇀ ⇂  
⇄ ⇅ 
⇋ ⥮
```
And avoiding these:
``` 
↽ ↿ ⇁ ⇃
⇆ ⇵
⇌ ⥯ 
```
### arrows with no completions
```
⤆   ⤇        ⟽ ⟾
⇠ ⇡ ⇢ ⇣
⇦ ⇧ ⇨ ⇩ ⬄ ⇳
⬅ ⬆ ⮕ ⬇ ⬌ ⬍
⇤ ⤒ ⇥ ⤓
⇷ ⤉ ⇸ ⤈ ⇹  
⇺ ⇞ ⇻ ⇟ ⇼
⤺   ⤻ ⤸ 
⇴ ⟴
```

