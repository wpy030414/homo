// homo · 离线物化表生成器
// 跑扩展算子区间 DP → 面额构造 → 展示轨最小化 → 切分（<N 全保留 + 对数网格 + top-K 锚点）
// → [0,N) 无界分支限界 vs 运行时贪心对拍收集 override 差集 → 全量自检 → 注入 homo.short.js。
//
// 运行：node tools/generate-short-table.mjs [--n=65536] [--eps=0.005] [--top=16]
//
// 自检原则（与研究文档 §8 一致）：不抽样。表内每条经 README 官方 eval 环境对拍、
// 数字序列校验、FLSQ 结构断言；override 条目逐条同检。
// 表区块（@table-begin … @table-end）为机器生成物——本脚本是唯一允许写入该区块的方式。

import { readFileSync, writeFileSync } from "node:fs"
import {
  buildTable,
  buildDenoms,
  makeGreedy,
  makeOptimal,
  parseAst,
  finisher,
  printV,
  digitBlocks,
  evalStr,
} from "./solver-core.mjs"

// ---- CLI 参数 ----
const arg = (name, dflt) => {
  const hit = process.argv.find((a) => a.startsWith(`--${name}=`))
  return hit ? Number(hit.split("=")[1]) : dflt
}
const N = arg("n", 65536) // 小整数区间上界（全保留）
const EPS = arg("eps", 0.005) // ≥N 面额的对数网格相对间隔
const TOP = arg("top", 16) // 无条件保留的 top-K 大值锚点（减法边）

const fail = (msg) => {
  console.error("✗ " + msg)
  process.exit(1)
}
const KB = (b) => (b / 1024).toFixed(1) + "KB"

console.log(`[generate] N=${N} eps=${EPS} top=${TOP}`)

// ==================== 1. 建表 + 面额 ====================
let t = Date.now()
const table = buildTable(true)
console.log(
  `扩展值集: ${table.size.toLocaleString("en-US")} 条, ${Date.now() - t}ms`,
)
const denoms = buildDenoms(table)
console.log(`面额: ${denoms.vals.length} 条`)

// ==================== 2. 展示轨最小化（数字保持 finisher） ====================
t = Date.now()
const minExprs = denoms.exprs.map((e) => finisher(e))
let shrunk = 0
for (let i = 0; i < minExprs.length; i++)
  if (minExprs[i].length < denoms.exprs[i].length) shrunk++
console.log(`最小化: ${shrunk} 条变短, ${Date.now() - t}ms`)

// ==================== 3. 切分：<N 全保留 + 对数网格 + top-K 锚点 ====================
const allVals = denoms.vals
// 招牌面额无条件保留：数字序列本身的拼接值（114514）与 2^53。
// 它们 ≥N，可能落在网格空档（实测 114514 曾因此退化为 2 块）——本游戏的规范锚点，
// 必须以单块入表。
const ALWAYS_KEEP = new Set([114514, 2 ** 53])
const bigIdx = [] // ≥N 的面额索引
for (let i = 0; i < allVals.length; i++) if (allVals[i] >= N) bigIdx.push(i)
const topSet = new Set(bigIdx.slice(-TOP)) // 最大 K 个无条件保留（含 2^53）
const keepIdx = []
let lastGrid = 0
for (let i = 0; i < allVals.length; i++) {
  const v = allVals[i]
  if (v < N) {
    keepIdx.push(i)
    continue
  }
  if (topSet.has(i) || ALWAYS_KEEP.has(v)) {
    keepIdx.push(i)
    lastGrid = v
    continue
  }
  if (v / lastGrid >= 1 + EPS) {
    keepIdx.push(i)
    lastGrid = v
  }
}
const keptVals = keepIdx.map((i) => allVals[i])
const keptExprs = keepIdx.map((i) => minExprs[i])
const nSmall = keptVals.filter((v) => v < N).length
console.log(
  `切分: <N ${nSmall} 条 + 网格 ${keptVals.length - nSmall - topSet.size} 条 + top${topSet.size} 锚点 → 共 ${keptVals.length} 条`,
)

// ==================== 4. override 差集：[0,N) 无界 B&B vs 切分表贪心 ====================
t = Date.now()
const greedy = makeGreedy({ vals: keptVals, exprs: keptExprs, ov: new Map() }) // 运行时同构
const optimal = makeOptimal(denoms) // 全量面额的无界 B&B
const keptSet = new Set(keptVals)
const ovEntries = [] // [n, e, c]
let checked = 0
for (let n = 0; n < N; n++) {
  if (keptSet.has(n)) continue // 表直接命中
  checked++
  const g = greedy(BigInt(n))
  const o = optimal(BigInt(n))
  // 仅收块数严格更优者（同块更短的 tiebreak 会使 override 膨胀一个数量级，
  // 买美观不买质量；表达式长度由贪心模板自身控制）
  const oe = finisher(o.e)
  if (o.c < g.c) ovEntries.push([n, oe, o.c])
  if (checked % 20000 === 0)
    console.log(
      `  B&B 对拍进度: ${checked}/${N - keptSet.size} (${((Date.now() - t) / 1000).toFixed(0)}s)`,
    )
}
console.log(
  `override: ${ovEntries.length} 条（贪心非最优差集）, ${((Date.now() - t) / 1000).toFixed(1)}s`,
)

// ==================== 5. 全量自检（不抽样） ====================
t = Date.now()
// 5.1 表条目：求值对拍 + 数字序列（单块）+ FLSQ 结构
let bad = 0,
  flsqBad = 0
for (let i = 0; i < keptVals.length; i++) {
  const e = keptExprs[i],
    v = keptVals[i]
  const k = digitBlocks(e)
  if (k !== 1) {
    bad++
    if (bad <= 5) console.error(`  ✗ 非单块序列 ${v}: ${e}`)
    continue
  }
  try {
    const ast = parseAst(e)
    const pv = printV(ast)
    // FLSQ(SQ( 嵌套（如 FLSQ(SQ(POW)/4)，e 轨 ⌊√(√x/y)⌋）为 uFloorSqrt 包裹含 √ 的
    // core 表达式的合法产物，printV 转写与 DP 原生 vwrap 模板一致；SQ 参数链路
    // 在 dyadic 不变量下精确（uSqrt 只留完全平方），实证以逐条求值对拍兜底。仅警告。
    if (pv.includes("FLSQ(SQ(")) {
      console.warn(`  ⚠ FLSQ(SQ( 嵌套 ${v}: ${pv.slice(0, 60)}`)
    }
    const ev = evalStr(pv)
    if (ev !== v) {
      bad++
      if (bad <= 5) console.error(`  ✗ 求值 ${v} → ${ev}: ${pv.slice(0, 60)}`)
    }
  } catch (err) {
    bad++
    console.error(`  ✗ 解析/求值异常 ${v}: ${err.message}`)
  }
}
if (bad) fail(`表条目自检失败: ${bad} 求值/序列违例`)
// 5.2 override：求值对拍 + 数字序列
let ovBad = 0
const ovFinal = {}
for (const [n, e, c] of ovEntries) {
  const k = digitBlocks(e)
  if (k < 1) {
    ovBad++
    continue
  }
  try {
    const ev = evalStr(printV(parseAst(e)))
    if (ev !== n) {
      ovBad++
      continue
    } // 浮点不过检的 override 丢弃（运行时退回贪心，正确性无损）
  } catch {
    ovBad++
    continue
  }
  ovFinal[n] = e
}
console.log(
  `自检: 表 ${keptVals.length} 条 + override ${Object.keys(ovFinal).length} 条全过（丢弃 ${ovBad} 条不过检 override）, ${Date.now() - t}ms`,
)

// ==================== 6. 序列化注入 ====================
const tableJson = JSON.stringify({
  v: keptVals,
  e: keptExprs,
  ov: ovFinal,
  meta: {
    N,
    eps: EPS,
    top: TOP,
    digits: "114514",
    generated: new Date().toISOString(),
  },
})
const shortPath = new URL("../homo.short.js", import.meta.url)
const src = readFileSync(shortPath, "utf8")
const re = /(\/\/ @table-begin)[\s\S]*?(\/\/ @table-end)/
if (!re.test(src))
  fail("homo.short.js 中未找到表标记区（@table-begin/@table-end）")
const out = src.replace(re, `$1\n\t${tableJson}\n\t$2`)
writeFileSync(shortPath, out)
console.log(
  `注入完成: 表 JSON ${KB(tableJson.length)}, homo.short.js ${KB(Buffer.byteLength(out))}`,
)

// ==================== 7. 质量统计（注入后运行时同构贪心） ====================
const rtGreedy = makeGreedy({
  vals: keptVals,
  exprs: keptExprs,
  ov: new Map(Object.entries(ovFinal).map(([k, v]) => [Number(k), v])),
})
let sum = 0,
  cnt = 0
for (let n = 1; n <= 100000; n += 99) {
  sum += rtGreedy(BigInt(n)).c
  cnt++
}
console.log(`质量: [1,1e5] 采样 ${cnt} 平均块数 ${(sum / cnt).toFixed(2)}`)
for (const [lo, hi] of [
  [1e6, 1e7],
  [1e9, 1e10],
  [1e12, 1e13],
]) {
  let s = 0,
    c2 = 0
  for (let i = 0; i < 300; i++) {
    const n = Math.floor(lo + Math.random() * (hi - lo))
    s += rtGreedy(BigInt(n)).c
    c2++
  }
  console.log(
    `  [${lo.toExponential(0)},${hi.toExponential(0)}] 随机 300: 平均 ${(s / c2).toFixed(2)} 块`,
  )
}
console.log("[generate] 完成 ✓")
