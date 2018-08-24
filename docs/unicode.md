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
Unicode messed up some mathematical symbols. Notably `ℝ` and `𝕉` are different. There are some fonts where the second R won't render.
I have removed Mathematical Monospace and Sans-Serif because in Pragmata Pro the glyphs are identical to the ASCII letters.
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
∀ ∂ ∃ ∄ ∅ ∝ ∞ √ ∛ ∜ ∫ ∮ ∱ ∲ ∳ ∓ ±
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
⊲ ⊳ ⊴ ⊵         ∆ ∇
⊏ ⊐ ⊑ ⊒         ⊓ ⊔ 
⋐⋑            ⋒⋓

≃≄≅≇≈≉≊≋≍≎≏≐≑≒≓
≖≗≘≙≚≛≜≝≞≟≠≡≢≣
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

