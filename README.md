# 恶臭数字论证器

一个将任意数字分解成 114514 构成的公式的工具。每个"块"用尽 `114514` 的全部六个数字（顺序固定），块之间以 `+` `*` `-` 拼接，追求最短块数表示。

本仓库提供两个库，按体积/质量取舍选用：

| 库              | 体积                | 值域                    | 平均块数（[1,1e5]） | 说明                                  |
| --------------- | ------------------- | ----------------------- | ------------------- | ------------------------------------- |
| `homo.js`       | 14KB                | 四则                    | ~5.9                | 上游轻量版，硬编码表 + 贪心，加载即用 |
| `homo.short.js` | 422KB（gzip 107KB） | 四则 + `!` `⌊⌋` `√` `^` | **~1.9**            | 短表示版，离线物化表 + 纯贪心         |

短表示版把区间 DP、扩展算子值域生成与最优解搜索全部放在**离线阶段**（`tools/generate-short-table.mjs`），产物以紧凑 JSON 物化进 `homo.short.js`，经全量求值对拍与数字序列校验后提交。浏览器端**零 DP、零搜索、零 BigInt 大数运算**——加载即用，单次求解毫秒级恒定。算法研究与实验数据见 [docs/researches](./docs/researches/01-number-theory-solver.md)。

## 引用方式

### 短表示版（推荐）

```HTML
<script src="homo.short.js"></script>
<script>
let 恶臭 = homoShort(1919810);
// "⌊(11!+4!^5)/(1+4!)⌋+((11-4*51)*(-4!)+⌊114/(51+4)⌋)"
</script>
```

### 轻量版

```HTML
<script src="homo.js"></script>
<script>
let 恶臭 = homo(1919810);
// "(114514+114514)*(11-4+5/1-4)+(114*514+(114*51*4+(1145*(1+4)+11-4+5+1-4)))"
</script>
```

两库可同时加载（`homo.js` 在前）；此时短表示版亦挂到 `homo.short`，用 `homo.short(num)` 调用。

### CDN

```HTML
<script src="https://cdn.jsdelivr.net/gh/wpy030414/homo/src/homo.js"></script>
<script src="https://cdn.jsdelivr.net/gh/wpy030414/homo/src/homo.short.js"></script>
```

### Node

```js
const homo = require("homo")
const homoShort = require("homo.short")
```

## API

短表示版与轻量版函数签名一致（轻量版无 `evalStr`）：

- `homoShort(num)` → 展示用表达式，含 `!`、`√`、`⌊⌋`、`^` 记号
- `homoShort.evalStr(num)` → 可直接 `eval` 的表达式，需先注入下列函数：

```js
const F = (n) => {
  let r = 1
  for (let i = 2; i <= n; i++) r *= i
  return r
} // n!
const SQ = (x) => Math.sqrt(x) // √
const FL = Math.floor // ⌊⌋
const POW = (a, b) => a ** b // ^
const FLSQ = (x) => Math.floor(Math.sqrt(x)) // ⌊√⌋
```

```js
homoShort(1919) // "(1+1)^4*5!-1^4"
homoShort.evalStr(1919) // "POW(1+1,4)*F(5)-POW(1,4)"
```

> 极小小数（如 `1e-309`、`Number.MIN_VALUE`）分母超出 IEEE-754 表示范围时，改用科学计数发射（次正规走 `×2^(-1074)`，100% 精确 round-trip），避免 `(P)/(Q)` 分母溢出为 `Infinity` 导致求值得 0。

## 验证

```sh
node tools/verify.mjs
```

短表示表逐条全量求值对拍 + 数字序列校验（顺序敏感，确保完整使用 `114514`）+ 行为矩阵（整数 0..3000 密集、大数、小数、极小小数、负数）+ 预算生命周期架构回归 + 旧表回归 + 性能预算。

## 重新生成物化表

```sh
node tools/generate-short-table.mjs    # 可选 --n / --eps / --top 调参
node tools/verify.mjs                  # 生成后必验
```

`homo.short.js` 中 `// @table-begin … // @table-end` 之间的表区块为机器生成物，**勿手改**。
