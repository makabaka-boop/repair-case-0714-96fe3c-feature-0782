import { BREAK, SAME, type AdoptedVersion, type DocModel, type PaginateResult, type PageSide } from './types';

/** 导出块（与画面一致：边界标记原样写回 breakAfter/sameAfter）。 */
export interface ExportBlock {
  id: string | number;
  height: number;
  breakAfter?: boolean;
  sameAfter?: boolean;
}

export interface ExportPage {
  /** 1 起页号 */
  page: number;
  /** 面别：第 1 页正面，此后正反交替；仅双面文件写出 */
  side?: PageSide;
  /** 本页实际容量；仅双面文件写出（单面文件省略以保持旧结构不变） */
  capacity?: number;
  /** 1 起块号半开区间 */
  startBlock: number;
  endBlock: number;
  startId: string | number;
  endId: string | number;
  used: number;
  remaining: number;
}

export interface ExportDoc {
  pageHeight: number;
  /** 背面容量；仅双面文件写出，重新导入即恢复双面计算语义 */
  backPageHeight?: number;
  blocks: ExportBlock[];
  pagination: {
    pageCount: number;
    cost: number;
    pages: ExportPage[];
  };
  adoptedAt: string;
}

/**
 * 构造下载用 JSON：可被本工具重新导入（分页字段在导入时被忽略），
 * 也可供外部系统消费。内容严格反映采纳时刻的画面状态。
 *
 * 单面文件不写 backPageHeight，每页也不写 side/capacity，结构与旧版逐项一致；
 * 双面文件在顶层固化 backPageHeight，每页固化 side 与 capacity。
 */
export function buildExport(model: DocModel, result: PaginateResult, adoptedAt: string): ExportDoc {
  const n = model.blocks.length;
  const duplex = model.backPageHeight !== undefined;
  const blocks: ExportBlock[] = model.blocks.map((b, i) => {
    const out: ExportBlock = { id: b.id, height: b.height };
    if (i < n - 1) {
      if (b.edge === BREAK) out.breakAfter = true;
      else if (b.edge === SAME) out.sameAfter = true;
    }
    return out;
  });

  const pages: ExportPage[] = result.pages.map((p, idx) => {
    const out: ExportPage = {
      page: idx + 1,
      startBlock: p.start + 1,
      endBlock: p.end,
      startId: model.blocks[p.start].id,
      endId: model.blocks[p.end - 1].id,
      used: p.used,
      remaining: p.remaining,
    };
    if (duplex) {
      out.side = p.side ?? (idx % 2 === 0 ? 'front' : 'back');
      out.capacity = p.capacity;
    }
    return out;
  });

  return {
    pageHeight: model.pageHeight,
    ...(duplex ? { backPageHeight: model.backPageHeight } : {}),
    blocks,
    pagination: { pageCount: result.pages.length, cost: result.cost, pages },
    adoptedAt,
  };
}

export function buildAdoptedExport(adopted: AdoptedVersion): ExportDoc {
  return buildExport(adopted.model, adopted.result, adopted.adoptedAt);
}
