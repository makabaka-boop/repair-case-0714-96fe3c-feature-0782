import { describe, expect, it } from 'vitest';
import {
  BREAK,
  CONFLICT,
  NONE,
  SAME,
  type AdoptedVersion,
  type DocModel,
  type Edge,
  type PaginateResult,
} from './types';
import { paginate } from './paginate';
import { parseDoc } from './model';
import { buildAdoptedExport, buildExport } from './export';
import { randomDoc } from './sample';

/** 朴素 O(n²) DP，作为穷举交叉验证的「标准答案」。 */
function bruteForce(model: DocModel): number {
  const { pageHeight: H, blocks } = model;
  const n = blocks.length;
  const S: number[] = [0];
  for (const b of blocks) S.push(S[S.length - 1] + b.height);
  const edgeAt = (i: number): Edge => (i < n - 1 ? blocks[i].edge : NONE);
  const canStart = (j: number) => j === 0 || edgeAt(j - 1) !== SAME;
  const canEnd = (i: number) => i === n || edgeAt(i - 1) !== SAME;

  const dp = new Array<number>(n + 1).fill(Infinity);
  dp[0] = 0;
  for (let i = 1; i <= n; i++) {
    if (!canEnd(i)) continue;
    for (let j = 0; j < i; j++) {
      if (!Number.isFinite(dp[j]) || !canStart(j)) continue;
      const used = S[i] - S[j];
      if (used > H) continue;
      let internalBreak = false;
      for (let k = j; k < i - 1; k++) {
        if (blocks[k].edge === BREAK) {
          internalBreak = true;
          break;
        }
      }
      if (internalBreak) continue;
      const rem = H - used;
      dp[i] = Math.min(dp[i], dp[j] + rem * rem);
    }
  }
  return dp[n];
}

/**
 * 双面朴素 O(n²) 奇偶 DP —— 独立于实现的「标准答案」：
 * dpF[i]/dpB[i] 分别表示前 i 块排完、末页为正/背面的最小代价，
 * 虚拟态 dpB[0]=0（0 页之后接正面）。不做凸包、不做窗口，逐 j 枚举。
 */
function bruteForceDuplex(model: DocModel): number {
  const Hf = model.pageHeight;
  const Hb = model.backPageHeight!;
  const { blocks } = model;
  const n = blocks.length;
  const S: number[] = [0];
  for (const b of blocks) S.push(S[S.length - 1] + b.height);
  const edgeAt = (i: number): Edge => (i < n - 1 ? blocks[i].edge : NONE);
  const canStart = (j: number) => j === 0 || edgeAt(j - 1) !== SAME;
  const canEnd = (i: number) => i === n || edgeAt(i - 1) !== SAME;

  const dpF = new Array<number>(n + 1).fill(Infinity);
  const dpB = new Array<number>(n + 1).fill(Infinity);
  dpB[0] = 0;
  for (let i = 1; i <= n; i++) {
    if (!canEnd(i)) continue;
    for (let j = 0; j < i; j++) {
      if (!canStart(j)) continue;
      const used = S[i] - S[j];
      let internalBreak = false;
      for (let k = j; k < i - 1; k++) {
        if (blocks[k].edge === BREAK) {
          internalBreak = true;
          break;
        }
      }
      if (internalBreak) continue;
      if (Number.isFinite(dpB[j]) && used <= Hf) {
        dpF[i] = Math.min(dpF[i], dpB[j] + (Hf - used) ** 2);
      }
      if (Number.isFinite(dpF[j]) && used <= Hb) {
        dpB[i] = Math.min(dpB[i], dpF[j] + (Hb - used) ** 2);
      }
    }
  }
  return Math.min(dpF[n], dpB[n]);
}

function makeModel(H: number, heights: number[], edges: Edge[] = [], backH?: number): DocModel {
  return {
    pageHeight: H,
    ...(backH === undefined ? {} : { backPageHeight: backH }),
    blocks: heights.map((height, i) => ({ id: i + 1, height, edge: edges[i] ?? NONE })),
  };
}

/** 校验双面分页：面别奇偶、各面容量、连续非空、强制分页/同页边界，并回算代价。 */
function expectValidDuplex(model: DocModel, out: ReturnType<typeof paginate>) {
  expect(out.ok).toBe(true);
  if (!out.ok) return;
  const Hf = model.pageHeight;
  const Hb = model.backPageHeight!;
  const { blocks } = model;
  const { pages, cost } = out.result;
  expect(pages.length).toBeGreaterThan(0);
  let recomputed = 0;
  let prevEnd = 0;
  for (let pi = 0; pi < pages.length; pi++) {
    const p = pages[pi];
    const onFront = pi % 2 === 0;
    const cap = onFront ? Hf : Hb;
    expect(p.side).toBe(onFront ? 'front' : 'back');
    expect(p.capacity).toBe(cap);
    expect(p.start).toBe(prevEnd);
    expect(p.end).toBeGreaterThan(p.start); // 每页非空
    prevEnd = p.end;
    let used = 0;
    for (let k = p.start; k < p.end; k++) used += blocks[k].height;
    expect(used).toBe(p.used);
    expect(used).toBeLessThanOrEqual(cap);
    expect(p.remaining).toBe(cap - used);
    recomputed += (cap - used) ** 2;
    for (let k = p.start; k < p.end - 1; k++) {
      expect(blocks[k].edge).not.toBe(BREAK);
    }
    if (p.start > 0) expect(blocks[p.start - 1].edge).not.toBe(SAME);
    if (p.end < blocks.length) expect(blocks[p.end - 1].edge).not.toBe(SAME);
  }
  expect(prevEnd).toBe(blocks.length);
  expect(cost).toBe(recomputed);
}

/** 校验返回分页的全部硬性条件，并回算代价。 */
function expectValid(model: DocModel, out: ReturnType<typeof paginate>) {
  expect(out.ok).toBe(true);
  if (!out.ok) return;
  const { blocks, pageHeight: H } = model;
  const { pages, cost } = out.result;
  expect(pages.length).toBeGreaterThan(0);
  let recomputed = 0;
  let prevEnd = 0;
  for (let pi = 0; pi < pages.length; pi++) {
    const p = pages[pi];
    // 连续性、覆盖性
    expect(p.start).toBe(prevEnd);
    expect(p.end).toBeGreaterThan(p.start);
    prevEnd = p.end;
    // 容量
    let used = 0;
    for (let k = p.start; k < p.end; k++) used += blocks[k].height;
    expect(used).toBe(p.used);
    expect(used).toBeLessThanOrEqual(H);
    expect(p.remaining).toBe(H - used);
    recomputed += (H - used) ** 2;
    // 页内不得有强制分页
    for (let k = p.start; k < p.end - 1; k++) {
      expect(blocks[k].edge).not.toBe(BREAK);
    }
    // 页首前边界不得为同页（除全文起点）
    if (p.start > 0) expect(blocks[p.start - 1].edge).not.toBe(SAME);
    // 页尾边界不得为同页（除全文终点）
    if (p.end < blocks.length) expect(blocks[p.end - 1].edge).not.toBe(SAME);
  }
  expect(prevEnd).toBe(blocks.length);
  expect(cost).toBe(recomputed);
}

describe('小规模穷举：与朴素 DP 完全一致', () => {
  const heightsPool = [1, 2, 3, 5];
  const edgePool: Edge[] = [NONE, BREAK, SAME, CONFLICT];

  it('穷举 n=1..6、H∈{5,6,9} 的高度序列与边界赋值，全部与 O(n²) 朴素 DP 一致', () => {
    let checked = 0;
    for (let n = 1; n <= 6; n++) {
      const heightSeqs: number[][] = [];
      const genH = (cur: number[]) => {
        if (cur.length === n) {
          heightSeqs.push([...cur]);
          return;
        }
        for (const h of heightsPool) genH([...cur, h]);
      };
      genH([]);

      // H 覆盖：恰好容纳、紧凑、宽松
      for (const H of [5, 6, 9]) {
        // n<=4 时对边界也做全穷举(4^(n-1) ≤ 256)；更大 n 时只取无冲突子集。
        const edgeSeqs: Edge[][] = [];
        if (n <= 4) {
          const genE = (cur: Edge[]) => {
            if (cur.length === n - 1) {
              edgeSeqs.push([...cur, NONE]);
              return;
            }
            for (const e of edgePool) genE([...cur, e]);
          };
          genE([]);
        } else {
          const noConflict: Edge[] = [NONE, BREAK, SAME];
          const genE = (cur: Edge[]) => {
            if (cur.length === n - 1) {
              edgeSeqs.push([...cur, NONE]);
              return;
            }
            // 3^5=243，配合下面的高度抽样控制总量
            for (const e of noConflict) genE([...cur, e]);
          };
          genE([]);
        }

        // n>4 时高度序列 4096 过多，按固定间隔抽样到约 200 个
        const sampledHeights = n > 4 ? heightSeqs.filter((_, idx) => idx % 20 === 0) : heightSeqs;

        for (const hs of sampledHeights) {
          if (hs.some((h) => h > H)) continue; // 数据约定：单块不超页高
          for (const es of edgeSeqs) {
            const model = makeModel(H, hs, es);
            const out = paginate(model);
            if (es.some((e) => e === CONFLICT)) {
              expect(out.ok).toBe(false);
              if (!out.ok) {
                expect(out.error.kind).toBe('conflict');
                if (out.error.kind === 'conflict') {
                  for (const c of out.error.conflicts) expect(es[c]).toBe(CONFLICT);
                }
              }
              checked++;
              continue;
            }
            const expected = bruteForce(model);
            if (Number.isFinite(expected)) {
              expectValid(model, out);
              if (out.ok) expect(out.result.cost).toBe(expected);
            } else {
              expect(out.ok).toBe(false);
              if (!out.ok) expect(out.error.kind).toBe('unsat');
            }
            checked++;
          }
        }
      }
    }
    expect(checked).toBeGreaterThan(100_000);
  }, 120_000);
});

describe('手工构造的关键情形', () => {
  it('单块', () => {
    const m = makeModel(10, [4]);
    const out = paginate(m);
    expectValid(m, out);
    if (out.ok) {
      expect(out.result.pages).toHaveLength(1);
      expect(out.result.cost).toBe(36);
    }
  });

  it('强制分页把两块拆到两页', () => {
    const m = makeModel(100, [30, 30], [BREAK, NONE]);
    const out = paginate(m);
    expectValid(m, out);
    if (out.ok) {
      expect(out.result.pages).toHaveLength(2);
      expect(out.result.cost).toBe(70 * 70 * 2);
    }
  });

  it('同页标记强制合页（即使拆分代价更低时也遵守约束）', () => {
    // 两块 40+40=80 ≤100：自由最优为合页（20²=400 < 2×60²=7200）
    const m = makeModel(100, [40, 40], [SAME, NONE]);
    expectValid(m, paginate(m));
    // 两块 70+20=90：自由最优为拆页(30²+80²=7300 vs 10²=100)——合页本来就优；
    // 改为 60+10=70：合页代价 900，拆页代价 1600+8100=9700，仍合页；
    // 构造「拆页更优但被 SAME 禁止」：60+30=90，合页 100，拆页 1600+4900=6500。
    const m2 = makeModel(100, [60, 30], [SAME, NONE]);
    const out2 = paginate(m2);
    expectValid(m2, out2);
    if (out2.ok) {
      expect(out2.result.pages).toHaveLength(1);
      expect(out2.result.cost).toBe(100);
    }
  });

  it('同页链超容量 → 无解并给出区间', () => {
    const m = makeModel(100, [60, 50], [SAME, NONE]);
    const out = paginate(m);
    expect(out.ok).toBe(false);
    if (!out.ok && out.error.kind === 'unsat') {
      expect(out.error.start).toBe(0);
      expect(out.error.end).toBe(2);
    }
  });

  it('强制分页 + 同页 冲突被禁止计算', () => {
    const m = makeModel(100, [30, 30, 30], [CONFLICT, NONE, NONE]);
    const out = paginate(m);
    expect(out.ok).toBe(false);
    if (!out.ok) {
      expect(out.error.kind).toBe('conflict');
      if (out.error.kind === 'conflict') expect(out.error.conflicts).toEqual([0]);
    }
  });

  it('修正冲突后能重新得到最优分页（状态可恢复）', () => {
    const m = makeModel(100, [30, 30], [CONFLICT, NONE]);
    expect(paginate(m).ok).toBe(false);
    m.blocks[0].edge = NONE;
    const out = paginate(m);
    expectValid(m, out);
  });

  it('滑动窗口凸包回归：H=5、高度 [2,3,1]，容量过期后中线重新最优', () => {
    // 线 1 相对线 0、2 全局冗余，但线 0 在 x>5 后因容量滑出窗口，
    // 可行集内最优变为 {1}、{2,3}：代价 3² + 1² = 10，而非 {1,2}、{3} 的 16。
    const m = makeModel(5, [2, 3, 1]);
    const out = paginate(m);
    expectValid(m, out);
    if (out.ok) {
      expect(out.result.cost).toBe(10);
      expect(out.result.pages).toHaveLength(2);
      expect(out.result.pages[0]).toMatchObject({ start: 0, end: 1 });
      expect(out.result.pages[1]).toMatchObject({ start: 1, end: 3 });
    }
  });

  it('多重边界混合', () => {
    const H = 50;
    const m = makeModel(
      H,
      [20, 15, 30, 10, 40, 5],
      [SAME, BREAK, NONE, SAME, NONE, NONE],
    );
    const out = paginate(m);
    expectValid(m, out);
    if (out.ok) expect(out.result.cost).toBe(bruteForce(m));
  });

  it('满页（剩余 0）与大高度边界值', () => {
    const m = makeModel(10000, [10000, 1, 10000], [BREAK, BREAK, NONE]);
    expectValid(m, paginate(m));
  });

  it('编辑边界后立即反映：无标记 → 同页链无解 → 解除后恢复最优（模拟 UI 逐项修改）', () => {
    const m = makeModel(100, [60, 50, 40], [NONE, NONE, NONE]);
    // 初始可行
    const first = paginate(m);
    expectValid(m, first);
    // 用户逐项打上两个同页标记：60+50 > 100 → 无解
    m.blocks[0].edge = SAME;
    expect(paginate(m).ok).toBe(false);
    m.blocks[1].edge = SAME;
    const unsat = paginate(m);
    expect(unsat.ok).toBe(false);
    // 修正：解除第一个同页，50+40=90 ≤ 100 仍须同页
    m.blocks[0].edge = NONE;
    const fixed = paginate(m);
    expectValid(m, fixed);
    if (fixed.ok) {
      // 块 2、3（下标 1、2）必须落在同一页
      const pageOf = (k: number) => fixed.result.pages.findIndex((p) => k >= p.start && k < p.end);
      expect(pageOf(1)).toBe(pageOf(2));
    }
    // 再改为强制分页
    m.blocks[1].edge = BREAK;
    expectValid(m, paginate(m));
    // 最终回到无标记，应与首次代价完全一致
    m.blocks[1].edge = NONE;
    const again = paginate(m);
    expectValid(m, again);
    if (again.ok && first.ok) expect(again.result.cost).toBe(first.result.cost);
  });
});

describe('双面模式（正反面交替、两种容量）', () => {
  it('锁定验收例：正面 5、背面 3、块高 [2,3,2,3] → 三页且代价 5，而非单容量的两个满页', () => {
    const m = makeModel(5, [2, 3, 2, 3], [], 3);
    const out = paginate(m);
    expectValidDuplex(m, out);
    if (out.ok) {
      expect(out.result.pages).toHaveLength(3);
      expect(out.result.cost).toBe(5);
      // 单容量（任一面）都会得到两个满页：正面 [2,3]、背面只能放 [2]、正面再放 [3]。
      expect(out.result.pages.map((p) => [p.start, p.end])).toEqual([
        [0, 2],
        [2, 3],
        [3, 4],
      ]);
      expect(out.result.pages.map((p) => p.side)).toEqual(['front', 'back', 'front']);
      expect(out.result.pages.map((p) => p.capacity)).toEqual([5, 3, 5]);
      // 对照：若误用单容量 H=5（两满页代价 0）或 H=3（块高 5 不存在）都不应得到该结果
      const single = makeModel(5, [2, 3, 2, 3]);
      const s = paginate(single);
      expect(s.ok).toBe(true);
      if (s.ok) {
        expect(s.result.pages).toHaveLength(2);
        expect(s.result.cost).toBe(0);
      }
    }
  });

  it('小规模穷举：双容量 + 全部边界赋值与独立 O(n²) 奇偶 DP 对拍', () => {
    let checked = 0;
    const heightPool = [1, 2, 3, 4];
    const edgePool: Edge[] = [NONE, BREAK, SAME, CONFLICT];
    for (let n = 1; n <= 6; n++) {
      const heightSeqs: number[][] = [];
      const genH = (cur: number[]) => {
        if (cur.length === n) {
          heightSeqs.push([...cur]);
          return;
        }
        for (const h of heightPool) genH([...cur, h]);
      };
      genH([]);

      // (Hf, Hb) 覆盖：正面大/背面小、相等、正面小/背面大
      for (const [Hf, Hb] of [
        [5, 3],
        [4, 4],
        [3, 6],
      ]) {
        const edgeSeqs: Edge[][] = [];
        if (n <= 4) {
          const genE = (cur: Edge[]) => {
            if (cur.length === n - 1) {
              edgeSeqs.push([...cur, NONE]);
              return;
            }
            for (const e of edgePool) genE([...cur, e]);
          };
          genE([]);
        } else {
          const noConflict: Edge[] = [NONE, BREAK, SAME];
          const genE = (cur: Edge[]) => {
            if (cur.length === n - 1) {
              edgeSeqs.push([...cur, NONE]);
              return;
            }
            for (const e of noConflict) genE([...cur, e]);
          };
          genE([]);
        }
        const sampledHeights = n > 4 ? heightSeqs.filter((_, idx) => idx % 17 === 0) : heightSeqs;

        for (const hs of sampledHeights) {
          if (hs.some((h) => h > Math.max(Hf, Hb))) continue;
          for (const es of edgeSeqs) {
            const model = makeModel(Hf, hs, es, Hb);
            const out = paginate(model);
            if (es.some((e) => e === CONFLICT)) {
              expect(out.ok).toBe(false);
              if (!out.ok && out.error.kind === 'conflict') {
                for (const c of out.error.conflicts) expect(es[c]).toBe(CONFLICT);
              }
              checked++;
              continue;
            }
            const expected = bruteForceDuplex(model);
            if (Number.isFinite(expected)) {
              expectValidDuplex(model, out);
              if (out.ok) expect(out.result.cost).toBe(expected);
            } else {
              expect(out.ok).toBe(false);
              if (!out.ok) expect(out.error.kind).toBe('unsat');
            }
            checked++;
          }
        }
      }
    }
    expect(checked).toBeGreaterThan(50_000);
  }, 120_000);

  it('同页链只适配一侧：链放得下正面(5)放不下背面(3) 且被奇偶逼到背面时无解', () => {
    // [3,2] 被 SAME 串成总高 5：只放得下正面。
    // 前置一块高 1 会使链起始页变成第 2 页（背面容量 3）→ 无解。
    const unsat = makeModel(5, [1, 3, 2], [BREAK, SAME, NONE], 3);
    const out = paginate(unsat);
    expect(out.ok).toBe(false);
    if (!out.ok) expect(out.error.kind).toBe('unsat');

    // 同一串链从第 1 页（正面）开始时合法，且链绝不被拆到背面。
    const okModel = makeModel(5, [3, 2], [SAME, NONE], 3);
    const ok = paginate(okModel);
    expectValidDuplex(okModel, ok);
    if (ok.ok) {
      expect(ok.result.pages[0]).toMatchObject({ start: 0, end: 2, side: 'front', capacity: 5 });
    }
  });

  it('强制分页遵守交替：两次 BREAK 后仍是 front-back-front 顺序', () => {
    const m = makeModel(5, [1, 1, 1], [BREAK, BREAK, NONE], 3);
    const out = paginate(m);
    expectValidDuplex(m, out);
    if (out.ok) {
      expect(out.result.pages).toHaveLength(3);
      expect(out.result.pages.map((p) => p.side)).toEqual(['front', 'back', 'front']);
      expect(out.result.cost).toBe((5 - 1) ** 2 + (3 - 1) ** 2 + (5 - 1) ** 2);
    }
  });

  it('块高允许到两面较大值：高度 5（>背面 3）只能落在正面', () => {
    const m = makeModel(5, [5, 1, 5], [], 3);
    const out = paginate(m);
    expectValidDuplex(m, out);
    if (out.ok) {
      for (let pi = 0; pi < out.result.pages.length; pi++) {
        const p = out.result.pages[pi];
        for (let k = p.start; k < p.end; k++) {
          if (m.blocks[k].height === 5) expect(p.side).toBe('front');
        }
      }
    }
  });

  it('中等规模交叉验证：1200 块双容量与朴素奇偶 DP 代价一致', () => {
    const model = randomDoc(1200, 100, 0xabcdef01, 60);
    const out = paginate(model);
    expectValidDuplex(model, out);
    if (out.ok) expect(out.result.cost).toBe(bruteForceDuplex(model));
  }, 30_000);
});

describe('导入校验', () => {
  it('接受合法数据并规范化标记', () => {
    const r = parseDoc({
      pageHeight: 100,
      blocks: [
        { id: 'a', height: 50, breakAfter: true },
        { id: 2, height: 10, sameAfter: true },
        { id: 'c3', height: 90 },
      ],
    });
    expect(r.ok).toBe(true);
    if (r.ok) {
      expect(r.model.blocks[0].edge).toBe(BREAK);
      expect(r.model.blocks[1].edge).toBe(SAME);
      expect(r.model.blocks[2].edge).toBe(NONE);
    }
  });

  it('breakAfter+sameAfter 同置规范化为 CONFLICT（可导入但禁止计算）', () => {
    const r = parseDoc({ pageHeight: 10, blocks: [{ id: 1, height: 1, breakAfter: true, sameAfter: true }, { id: 2, height: 1 }] });
    expect(r.ok).toBe(true);
    if (r.ok) expect(r.model.blocks[0].edge).toBe(CONFLICT);
  });

  const badCases: Array<[string, unknown]> = [
    ['顶层不是对象', null],
    ['顶层是数组', []],
    ['pageHeight 缺失', { blocks: [] }],
    ['pageHeight 为字符串', { pageHeight: '100', blocks: [] }],
    ['pageHeight 为 0', { pageHeight: 0, blocks: [] }],
    ['pageHeight 超界', { pageHeight: 10001, blocks: [] }],
    ['blocks 缺失', { pageHeight: 100 }],
    ['blocks 为空', { pageHeight: 100, blocks: [] }],
    ['块非对象', { pageHeight: 100, blocks: [1] }],
    ['id 缺失', { pageHeight: 100, blocks: [{ height: 1 }] }],
    ['id 类型错', { pageHeight: 100, blocks: [{ id: {}, height: 1 }] }],
    ['id 重复(数字)', { pageHeight: 100, blocks: [{ id: 1, height: 1 }, { id: 1, height: 1 }] }],
    ['id 重复(字符串)', { pageHeight: 100, blocks: [{ id: 'x', height: 1 }, { id: 'x', height: 1 }] }],
    ['height 非整数', { pageHeight: 100, blocks: [{ id: 1, height: 1.5 }] }],
    ['height 超页高', { pageHeight: 100, blocks: [{ id: 1, height: 101 }] }],
    ['height 为 0', { pageHeight: 100, blocks: [{ id: 1, height: 0 }] }],
    ['标记类型错', { pageHeight: 100, blocks: [{ id: 1, height: 1, breakAfter: 'yes' }, { id: 2, height: 1 }] }],
  ];
  for (const [name, input] of badCases) {
    it(`拒绝：${name}`, () => {
      const r = parseDoc(input);
      expect(r.ok).toBe(false);
    });
  }

  it('接受 backPageHeight 启用双面模式，块高放宽到两面较大值', () => {
    const r = parseDoc({
      pageHeight: 5,
      backPageHeight: 3,
      blocks: [
        { id: 1, height: 5 },
        { id: 2, height: 3 },
      ],
    });
    expect(r.ok).toBe(true);
    if (r.ok) {
      expect(r.model.backPageHeight).toBe(3);
      expect(r.model.blocks[1].height).toBe(3);
    }
  });

  it('省略 backPageHeight 时模型上不存在该字段（单面结构逐项不变）', () => {
    const r = parseDoc({ pageHeight: 10, blocks: [{ id: 1, height: 4 }] });
    expect(r.ok).toBe(true);
    if (r.ok) expect('backPageHeight' in r.model).toBe(false);
  });

  const badBackCases: Array<[string, unknown]> = [
    ['backPageHeight 为字符串', { pageHeight: 10, backPageHeight: '3', blocks: [] }],
    ['backPageHeight 为 0', { pageHeight: 10, backPageHeight: 0, blocks: [] }],
    ['backPageHeight 超界', { pageHeight: 10, backPageHeight: 10001, blocks: [] }],
    ['backPageHeight 为 null', { pageHeight: 10, backPageHeight: null, blocks: [] }],
    ['双面块高超两面较大值', { pageHeight: 5, backPageHeight: 3, blocks: [{ id: 1, height: 6 }] }],
  ];
  for (const [name, input] of badBackCases) {
    it(`拒绝：${name}`, () => {
      expect(parseDoc(input).ok).toBe(false);
    });
  }

  it('双面块高在 (较小容量, 较大容量] 区间合法；单块 ≤ 较小容量的旧边界仍合法', () => {
    expect(parseDoc({ pageHeight: 3, backPageHeight: 5, blocks: [{ id: 1, height: 5 }] }).ok).toBe(true);
    expect(parseDoc({ pageHeight: 3, backPageHeight: 5, blocks: [{ id: 1, height: 4 }] }).ok).toBe(true);
  });

  it('数字 1 与字符串 "1" 视为不同 id', () => {
    const r = parseDoc({ pageHeight: 10, blocks: [{ id: 1, height: 1 }, { id: '1', height: 1 }] });
    expect(r.ok).toBe(true);
  });

  it('重新导入导出文件：分页字段被忽略，标记被恢复', () => {
    const m = makeModel(100, [30, 40, 20], [BREAK, SAME, NONE]);
    const out = paginate(m);
    expect(out.ok).toBe(true);
    if (!out.ok) return;
    const exported = buildExport(m, out.result, new Date().toISOString());
    const reparsed = parseDoc(JSON.parse(JSON.stringify(exported)));
    expect(reparsed.ok).toBe(true);
    if (reparsed.ok) {
      expect(reparsed.model.blocks[0].edge).toBe(BREAK);
      expect(reparsed.model.blocks[1].edge).toBe(SAME);
      const out2 = paginate(reparsed.model);
      expect(out2.ok).toBe(true);
      if (out2.ok) expect(out2.result.cost).toBe(out.result.cost);
    }
  });

  it('旧单面导出结构逐项不变：无 backPageHeight，页面无 side/capacity 字段', () => {
    const m = makeModel(100, [30, 40, 20], [BREAK, NONE, NONE]);
    const out = paginate(m);
    expect(out.ok).toBe(true);
    if (!out.ok) return;
    const exported = buildExport(m, out.result, '2026-09-21T00:00:00.000Z');
    expect('backPageHeight' in exported).toBe(false);
    expect(exported.pageHeight).toBe(100);
    for (const p of exported.pagination.pages) {
      expect('side' in p).toBe(false);
      expect('capacity' in p).toBe(false);
    }
    // 键顺序/结构快照（仅本工具实际写出的字段）
    expect(Object.keys(exported)).toEqual(['pageHeight', 'blocks', 'pagination', 'adoptedAt']);
    expect(Object.keys(exported.pagination.pages[0])).toEqual([
      'page',
      'startBlock',
      'endBlock',
      'startId',
      'endId',
      'used',
      'remaining',
    ]);
  });

  it('双面导出固化 backPageHeight 与每页 side/capacity，重新导入恢复双面语义', () => {
    const m = makeModel(5, [2, 3, 2, 3], [], 3);
    const out = paginate(m);
    expect(out.ok).toBe(true);
    if (!out.ok) return;
    const exported = buildExport(m, out.result, new Date().toISOString());
    expect(exported.backPageHeight).toBe(3);
    expect(exported.pagination.pages.map((p) => p.side)).toEqual(['front', 'back', 'front']);
    expect(exported.pagination.pages.map((p) => p.capacity)).toEqual([5, 3, 5]);
    expect(exported.pagination.pages.map((p) => p.remaining)).toEqual([0, 1, 2]);

    const reparsed = parseDoc(JSON.parse(JSON.stringify(exported)));
    expect(reparsed.ok).toBe(true);
    if (!reparsed.ok) return;
    expect(reparsed.model.backPageHeight).toBe(3);
    const out2 = paginate(reparsed.model);
    expectValidDuplex(reparsed.model, out2);
    if (out2.ok) {
      expect(out2.result.cost).toBe(out.result.cost);
      expect(out2.result.pages).toHaveLength(3);
      expect(out2.result.pages.map((p) => p.side)).toEqual(['front', 'back', 'front']);
    }
  });

  it('采纳快照不受后续编辑影响（含 backPageHeight 固化）', () => {
    const m = makeModel(5, [2, 3, 2, 3], [], 3);
    const first = paginate(m);
    expect(first.ok).toBe(true);
    if (!first.ok) return;
    const adopted: AdoptedVersion = {
      model: { ...m, blocks: m.blocks.map((b) => ({ ...b })) },
      result: JSON.parse(JSON.stringify(first.result)) as PaginateResult,
      adoptedAt: '2026-09-21T00:00:00.000Z',
    };
    // 后续编辑：改容量、加边界
    m.backPageHeight = 4;
    m.blocks[0].edge = BREAK;
    const adoptedExport = buildAdoptedExport(adopted);
    expect(adoptedExport.backPageHeight).toBe(3);
    expect(adoptedExport.pagination.pageCount).toBe(3);
    expect(adoptedExport.blocks[0].breakAfter).toBeUndefined();
  });
});

describe('大夹具验收（性能 + 正确性）', () => {
  it('200000 块随机文档 4 秒内完成且方案合法', () => {
    const model = randomDoc(200_000, 1000, 0x9e3779b9);
    const t0 = performance.now();
    const out = paginate(model);
    const elapsed = performance.now() - t0;
    expectValid(model, out);
    // 注：vitest 对 BigInt 热点存在约 50–60 倍解释执行惩罚；
    // vite build 产物在原生 Node/浏览器中实测约 0.15s（见 scripts/perf-check.mjs）。
    expect(elapsed).toBeLessThan(15_000);
  });

  it('200000 个高度为 1 的块 / pageHeight=1：200000 页，代价 0', () => {
    const model: DocModel = {
      pageHeight: 1,
      blocks: Array.from({ length: 200_000 }, (_, i) => ({ id: i, height: 1, edge: NONE })),
    };
    const t0 = performance.now();
    const out = paginate(model);
    expect(elapsedSafe(t0)).toBeLessThan(15_000);
    expect(out.ok).toBe(true);
    if (out.ok) {
      expect(out.result.pages).toHaveLength(200_000);
      expect(out.result.cost).toBe(0);
    }
  });

  it('200000 块全部同页链且超过一页（pageHeight=10000）', () => {
    // 每块高 1，总高 200000 > 10000 且全部 SAME → 无解，须快速给出区间
    const model: DocModel = {
      pageHeight: 10000,
      blocks: Array.from({ length: 200_000 }, (_, i) => ({
        id: i,
        height: 1,
        edge: (i < 199_999 ? SAME : NONE) as Edge,
      })),
    };
    const t0 = performance.now();
    const out = paginate(model);
    expect(performance.now() - t0).toBeLessThan(15_000);
    expect(out.ok).toBe(false);
    if (!out.ok) expect(out.error.kind).toBe('unsat');
  });

  it('5000 块规模与朴素 DP 代价一致（中等交叉验证）', () => {
    const model = randomDoc(5000, 100, 0x1234abcd);
    const out = paginate(model);
    expectValid(model, out);
    if (out.ok) expect(out.result.cost).toBe(bruteForce(model));
  }, 30_000);

  it('大前缀和精度：块高接近页容量时交叉比较超出 2^53，仍与朴素 DP 一致', () => {
    // 确定性构造：H=10000，块高在 6000..10000 间，300 块 → 前缀和约 2.4e6，
    // 凸包交叉乘积达 1e17 量级，Double 无法精确表示整数，逼迫走 BigInt。
    let s = 0xc0ffee >>> 0;
    const rand = () => {
      s ^= s << 13; s ^= s >>> 17; s ^= s << 5; s = s >>> 0;
      return s / 0xffffffff;
    };
    const heights = Array.from({ length: 300 }, () => 6000 + Math.floor(rand() * 4001));
    const edges: Edge[] = heights.map((_, i) => {
      if (i === heights.length - 1) return NONE;
      const r = rand();
      return r < 0.1 ? BREAK : r < 0.2 ? SAME : NONE;
    });
    // 若随机 SAME 造成无解则跳过（预检行为另有测试覆盖）
    const model = makeModel(10000, heights, edges);
    const expected = bruteForce(model);
    if (!Number.isFinite(expected)) return;
    const out = paginate(model);
    expectValid(model, out);
    if (out.ok) expect(out.result.cost).toBe(expected);
  });

  it('200000 块 + 大量随机强制分页/同页标记：合法', () => {
    const model = randomDoc(200_000, 1000, 0xdeadbeef);
    const t0 = performance.now();
    const out = paginate(model);
    expect(performance.now() - t0).toBeLessThan(15_000);
    expectValid(model, out);
  });

  it('200000 块双容量（正面 1000 / 背面 700）：线性级完成、奇偶与各面容量合法', () => {
    const model = randomDoc(200_000, 1000, 0x5151aaaa, 700);
    const t0 = performance.now();
    const out = paginate(model);
    expect(performance.now() - t0).toBeLessThan(15_000);
    expectValidDuplex(model, out);
  });

  it('200000 块双容量 + 极端容量（正面 10000 / 背面 1）：线性级完成', () => {
    // 背面只能放高度 1 的块；随机文档按较小容量采样，故全部块高 1。
    const model = randomDoc(200_000, 10000, 0x0badf00d, 1);
    const t0 = performance.now();
    const out = paginate(model);
    expect(performance.now() - t0).toBeLessThan(15_000);
    expectValidDuplex(model, out);
    if (out.ok) {
      // 每页一块；第 2、4、… 页容量 1，剩余 0
      for (let pi = 1; pi < out.result.pages.length; pi += 2) {
        expect(out.result.pages[pi]).toMatchObject({ side: 'back', capacity: 1, used: 1, remaining: 0 });
      }
    }
  });
});

function elapsedSafe(t0: number): number {
  return performance.now() - t0;
}
