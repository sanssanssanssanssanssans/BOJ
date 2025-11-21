use std::collections::{HashMap, HashSet, BinaryHeap};
use std::cmp::Reverse;
use std::io::{self, Write};
use std::f64;
use std::io::Read;
const INF: f64 = 1e100;
const EPS_DENOM: f64 = 1e-12;
const EPS_DISC: f64 = 1e-9;
const KEY_PREC_SCALE: f64 = 1e6;

#[inline]
fn ccw(ax: f64, ay: f64, bx: f64, by: f64, cx: f64, cy: f64) -> i32 {
    let v = (bx - ax) * (cy - ay) - (by - ay) * (cx - ax);
    if v > 0.0 { 1 } else if v < 0.0 { -1 } else { 0 }
}

#[inline]
fn segments_intersect(s1: &[f64;4], s2: &[f64;4]) -> bool {
    let (x1,y1,x2,y2) = (s1[0],s1[1],s1[2],s1[3]);
    let (x3,y3,x4,y4) = (s2[0],s2[1],s2[2],s2[3]);
    if x1.max(x2) < x3.min(x4) || x3.max(x4) < x1.min(x2) ||
       y1.max(y2) < y3.min(y4) || y3.max(y4) < y1.min(y2) {
        return false;
    }
    let o1 = ccw(x1,y1,x2,y2,x3,y3);
    let o2 = ccw(x1,y1,x2,y2,x4,y4);
    let o3 = ccw(x3,y3,x4,y4,x1,y1);
    let o4 = ccw(x3,y3,x4,y4,x2,y2);
    if o1==0 && o2==0 && o3==0 && o4==0 {
        let xi1 = x1.min(x2).max(x3.min(x4));
        let xi2 = x1.max(x2).min(x3.max(x4));
        let yi1 = y1.min(y2).max(y3.min(y4));
        let yi2 = y1.max(y2).min(y3.max(y4));
        return xi1 <= xi2 && yi1 <= yi2;
    }
    (o1 * o2 <= 0) && (o3 * o4 <= 0)
}

#[inline]
fn intersection_params(s1: &[f64;4], s2: &[f64;4]) -> (f64,f64,f64,f64) {
    let (x1,y1,x2,y2) = (s1[0],s1[1],s1[2],s1[3]);
    let (x3,y3,x4,y4) = (s2[0],s2[1],s2[2],s2[3]);
    let dx1 = x2 - x1; let dy1 = y2 - y1;
    let dx2 = x4 - x3; let dy2 = y4 - y3;
    let denom = dx1 * dy2 - dy1 * dx2;
    if denom.abs() < EPS_DENOM {
        let cand1 = [(x1,y1,0.0),(x2,y2,1.0)];
        let cand2 = [(x3,y3,0.0),(x4,y4,1.0)];
        for &(px,py,t1) in &cand1 {
            for &(qx,qy,t2) in &cand2 {
                if px == qx && py == qy {
                    return (px,py,t1,t2);
                }
            }
        }
        return (x1,y1,0.0,0.0);
    }
    let qpx = x3 - x1;
    let qpy = y3 - y1;
    let mut t1 = (qpx * dy2 - qpy * dx2) / denom;
    let mut t2 = (qpx * dy1 - qpy * dx1) / denom;
    let tiny = 1e-12;
    if t1 < 0.0 && t1 > -tiny { t1 = 0.0; }
    if t1 > 1.0 && t1 < 1.0 + tiny { t1 = 1.0; }
    if t2 < 0.0 && t2 > -tiny { t2 = 0.0; }
    if t2 > 1.0 && t2 < 1.0 + tiny { t2 = 1.0; }
    let x = x1 + t1 * dx1;
    let y = y1 + t1 * dy1;
    (x,y,t1,t2)
}

#[inline]
fn evalue_d(du: f64, dv: f64, l: f64, s: f64) -> f64 {
    let mut best = INF;
    if du < INF {
        let temp = du + s;
        if temp < best { best = temp; }
    }
    if dv < INF {
        let temp = dv + (l - s);
        if temp < best { best = temp; }
    }
    best
}

#[inline]
fn best_on_edge_intervalue(du: f64, dv: f64, l: f64, pL: f64, pR: f64) -> f64 {
    if du >= INF && dv >= INF { return INF; }
    let mut best = INF;
    let v = evalue_d(du, dv, l, pL);
    if v < best { best = v; }
    if (pR - pL).abs() > 0.0 {
        let v2 = evalue_d(du, dv, l, pR);
        if v2 < best { best = v2; }
    }
    if du < INF && dv < INF {
        let s_star = (dv - du + l) * 0.5;
        if s_star >= pL - 1e-12 && s_star <= pR + 1e-12 {
            let v3 = evalue_d(du, dv, l, s_star);
            if v3 < best { best = v3; }
        }
    }
    best
}

fn build_segtree(values: &Vec<f64>) -> (usize, Vec<f64>) {
    let m = values.len();
    if m == 0 { return (0, vec![]); }
    let mut n = 1usize;
    while n < m { n <<= 1; }
    let mut seg = vec![INF; 2*n];
    for i in 0..m { seg[n+i] = values[i]; }
    for i in (1..n).rev() {
        let l = seg[i<<1];
        let r = seg[(i<<1)|1];
        seg[i] = if l < r { l } else { r };
    }
    (n, seg)
}

fn seg_range_min(seg: &Vec<f64>, n: usize, mut l: usize, mut r: usize) -> f64 {
    if n == 0 || l >= r { return INF; }
    let mut res = INF;
    l += n; r += n;
    while l < r {
        if (l & 1) == 1 {
            if seg[l] < res { res = seg[l]; }
            l += 1;
        }
        if (r & 1) == 1 {
            r -= 1;
            if seg[r] < res { res = seg[r]; }
        }
        l >>= 1; r >>= 1;
    }
    res
}

#[derive(Clone, Default)]
struct SegmentData {
    sx: f64, sy: f64, ex: f64, ey: f64,
    len: f64,
    nodes: Vec<usize>,
    spos: Vec<f64>,
    edge_len: Vec<f64>,
    edge_min: Vec<f64>,
    st_n: usize,
    st_seg: Vec<f64>,
    usable: bool,
}

struct FastScanner {
    buf: Vec<u8>,
    idx: usize,
}
impl FastScanner {
    fn new() -> Self {
        let mut input = String::new();
        std::io::stdin().read_to_string(&mut input).unwrap();
        Self { buf: input.into_bytes(), idx: 0 }
    }
    #[inline] fn skip_ws(&mut self) {
        while self.idx < self.buf.len() {
            let c = self.buf[self.idx];
            if c==b' '||c==b'\n'||c==b'\r'||c==b'\t' { self.idx +=1; continue; }
            break;
        }
    }
    #[inline] fn next_i32(&mut self) -> i32 {
        self.skip_ws();
        let mut sign = 1;
        if self.buf[self.idx]==b'-' { sign = -1; self.idx+=1; }
        let mut val: i32 = 0;
        while self.idx < self.buf.len() {
            let c = self.buf[self.idx];
            if c < b'0' || c > b'9' { break; }
            val = val * 10 + (c - b'0') as i32;
            self.idx += 1;
        }
        val * sign
    }
    #[inline] fn next_usize(&mut self) -> usize {
        self.skip_ws();
        let mut val: usize = 0;
        while self.idx < self.buf.len() {
            let c = self.buf[self.idx];
            if c < b'0' || c > b'9' { break; }
            val = val * 10 + (c - b'0') as usize;
            self.idx += 1;
        }
        val
    }
    #[inline] fn next_f64(&mut self) -> f64 {
        self.skip_ws();
        let mut sign = 1.0;
        if self.buf[self.idx]==b'-' { sign = -1.0; self.idx+=1; }
        let mut intpart: i64 = 0;
        while self.idx < self.buf.len() {
            let c = self.buf[self.idx];
            if c < b'0' || c > b'9' { break; }
            intpart = intpart * 10 + (c - b'0') as i64;
            self.idx += 1;
        }
        let mut val = intpart as f64;
        if self.idx < self.buf.len() && self.buf[self.idx]==b'.' {
            self.idx += 1;
            let mut place = 0.1f64;
            while self.idx < self.buf.len() {
                let c = self.buf[self.idx];
                if c < b'0' || c > b'9' { break; }
                val += (c - b'0') as f64 * place;
                place *= 0.1;
                self.idx += 1;
            }
        }
        sign * val
    }
}

#[derive(Copy, Clone, PartialEq, PartialOrd)]
struct F64(f64);
impl Eq for F64 {}
impl Ord for F64 {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.total_cmp(&other.0)
    }
}

fn get_pid_fn(x: f64, y: f64, points: &mut Vec<(f64,f64)>, pidmap: &mut HashMap<i128,usize>) -> usize {
    let rx = (x * KEY_PREC_SCALE).round() as i64;
    let ry = (y * KEY_PREC_SCALE).round() as i64;
    let key: i128 = ((rx as i128) << 64) ^ (ry as i128 & 0xffff_ffff_ffff_ffffi128);
    if let Some(&id) = pidmap.get(&key) { return id; }
    let id = points.len();
    points.push((rx as f64 / KEY_PREC_SCALE, ry as f64 / KEY_PREC_SCALE));
    pidmap.insert(key, id);
    id
}

fn main() {
    let mut fs = FastScanner::new();
    let t = fs.next_i32() as usize;
    let mut out = String::with_capacity(1<<20);
    for _case in 0..t {
        let n = fs.next_i32() as usize;
        let r = fs.next_f64();
        let r2 = r * r;
        let mut segments: Vec<[f64;4]> = vec![[0.0;4]; n];
        let mut seg_pts: Vec<Vec<(f64,usize)>> = vec![vec![]; n];
        let mut total_fs = 0usize;
        let mut points: Vec<(f64,f64)> = Vec::new();
        let mut pidmap: HashMap<i128, usize> = HashMap::new();
        let mut fire_nodes: HashSet<usize> = HashSet::new();

        for i in 0..n {
            let sx = fs.next_f64();
            let sy = fs.next_f64();
            let ex = fs.next_f64();
            let ey = fs.next_f64();
            let m = fs.next_i32() as usize;
            segments[i] = [sx,sy,ex,ey];
            total_fs += m;
            let id_s = get_pid_fn(sx, sy, &mut points, &mut pidmap);
            let id_e = get_pid_fn(ex, ey, &mut points, &mut pidmap);
            seg_pts[i].push((0.0, id_s));
            seg_pts[i].push((1.0, id_e));
            for _ in 0..m {
                let c = fs.next_f64();
                let x = sx + (ex - sx) * c;
                let y = sy + (ey - sy) * c;
                let pid = get_pid_fn(x, y, &mut points, &mut pidmap);
                seg_pts[i].push((c, pid));
                fire_nodes.insert(pid);
            }
        }

        let q = fs.next_i32() as usize;
        let mut queries: Vec<(f64,f64)> = Vec::with_capacity(q);
        for _ in 0..q {
            let qx = fs.next_f64();
            let qy = fs.next_f64();
            queries.push((qx,qy));
        }

        if total_fs == 0 {
            for _ in 0..q { out.push_str("-1\n"); }
            continue;
        }

        for i in 0..n {
            for j in (i+1)..n {
                if !segments_intersect(&segments[i], &segments[j]) { continue; }
                let (x,y,t1,t2) = intersection_params(&segments[i], &segments[j]);
                let pid = get_pid_fn(x,y, &mut points, &mut pidmap);
                seg_pts[i].push((t1, pid));
                seg_pts[j].push((t2, pid));
            }
        }

        let nnodes = points.len();
        let mut adj: Vec<Vec<(usize,f64)>> = vec![Vec::new(); nnodes];
        let mut segdata: Vec<SegmentData> = vec![SegmentData::default(); n];

        for i in 0..n {
            let mut sp = seg_pts[i].clone();
            sp.sort_by(|a,b| {
                if a.0 == b.0 { a.1.cmp(&b.1) } else { a.0.partial_cmp(&b.0).unwrap() }
            });
            let mut unique: Vec<(f64,usize)> = Vec::with_capacity(sp.len());
            let mut last: isize = -1;
            for (t,pid) in sp {
                if last == pid as isize { continue; }
                unique.push((t,pid));
                last = pid as isize;
            }
            if unique.len() < 2 { continue; }
            let k = unique.len();
            let mut seg = SegmentData::default();
            seg.sx = segments[i][0]; seg.sy = segments[i][1];
            seg.ex = segments[i][2]; seg.ey = segments[i][3];
            seg.len = (seg.ex - seg.sx).hypot(seg.ey - seg.sy);
            seg.nodes = vec![0usize; k];
            seg.spos = vec![0f64; k];
            seg.edge_len = vec![0f64; k-1];
            let first_node = unique[0].1;
            seg.nodes[0] = first_node;
            seg.spos[0] = 0.0;
            let mut px = points[first_node].0;
            let mut py = points[first_node].1;
            for kk in 1..k {
                let node = unique[kk].1;
                seg.nodes[kk] = node;
                let qx = points[node].0; let qy = points[node].1;
                let ddx = qx - px; let ddy = qy - py;
                let L = ddx.hypot(ddy);
                seg.edge_len[kk-1] = L;
                seg.spos[kk] = seg.spos[kk-1] + L;
                let u = unique[kk-1].1; let v = node;
                if u != v && L >= 0.0 {
                    adj[u].push((v, L));
                    adj[v].push((u, L));
                }
                px = qx; py = qy;
            }
            seg.usable = false;
            seg.st_n = 0;
            segdata[i] = seg;
        }

        // multi-source Dijkstra using min-heap via Reverse(F64)
        let mut dist: Vec<f64> = vec![INF; nnodes];
        let mut heap: BinaryHeap<(Reverse<F64>, usize)> = BinaryHeap::new();
        for &src in fire_nodes.iter() {
            dist[src] = 0.0;
            heap.push((Reverse(F64(0.0)), src));
        }
        while let Some((Reverse(F64(d)), u)) = heap.pop() {
            if d != dist[u] { continue; }
            for &(v,w) in &adj[u] {
                let nd = d + w;
                if nd < dist[v] {
                    dist[v] = nd;
                    heap.push((Reverse(F64(nd)), v));
                }
            }
        }

        for i in 0..n {
            let seg = &mut segdata[i];
            let k = seg.nodes.len();
            if k < 2 { seg.usable = false; seg.st_n = 0; seg.st_seg.clear(); continue; }
            let m = k - 1;
            let mut edge_min = vec![INF; m];
            let mut anyfinite = false;
            for j in 0..m {
                let u = seg.nodes[j];
                let v = seg.nodes[j+1];
                let du = dist[u];
                let dv = dist[v];
                let L = seg.edge_len[j];
                if du >= INF && dv >= INF { edge_min[j] = INF; continue; }
                let mut best = INF;
                if du < INF && du < best { best = du; }
                if dv < INF && dv < best { best = dv; }
                if du < INF && dv < INF {
                    let s_star = (dv - du + L) * 0.5;
                    if s_star > 0.0 && s_star < L {
                        let value = evalue_d(du, dv, L, s_star);
                        if value < best { best = value; }
                    }
                }
                edge_min[j] = best;
                if best < INF { anyfinite = true; }
            }
            seg.edge_min = edge_min;
            seg.usable = anyfinite;
            if anyfinite {
                let (stn, stseg) = build_segtree(&seg.edge_min);
                seg.st_n = stn;
                seg.st_seg = stseg;
            } else {
                seg.st_n = 0;
                seg.st_seg.clear();
            }
        }

        for &(qx,qy) in &queries {
            let mut result = INF;
            for i in 0..n {
                let seg = &segdata[i];
                if !seg.usable { continue; }
                let sx = seg.sx; let sy = seg.sy;
                let ex = seg.ex; let ey = seg.ey;
                let dx = ex - sx; let dy = ey - sy;
                let ltot2 = dx*dx + dy*dy;
                if ltot2 <= 0.0 { continue; }
                let fx = sx - qx; let fy = sy - qy;
                let a = ltot2;
                let b = 2.0 * (dx * fx + dy * fy);
                let c = fx*fx + fy*fy - r2;
                let mut disc = b*b - 4.0*a*c;
                if disc < -EPS_DISC { continue; }
                if disc < 0.0 { disc = 0.0; }
                let sqrt_disc = disc.sqrt();
                let mut t1 = (-b - sqrt_disc) / (2.0*a);
                let mut t2 = (-b + sqrt_disc) / (2.0*a);
                if t1 > t2 { let tmp = t1; t1 = t2; t2 = tmp; }
                if t1 > 1.0 || t2 < 0.0 { continue; }
                let t_low = if t1 > 0.0 { t1 } else { 0.0 };
                let t_high = if t2 < 1.0 { t2 } else { 1.0 };
                if t_low > t_high { continue; }
                let ltot = seg.len;
                if ltot <= 0.0 { continue; }
                let mut sL = ltot * t_low;
                let mut sR = ltot * t_high;
                if sL > sR { let tmp = sL; sL = sR; sR = tmp; }
                let spos = &seg.spos;
                let end_s = *spos.last().unwrap();
                if sL < 0.0 { sL = 0.0; }
                if sR > end_s { sR = end_s; }
                if sR < sL { continue; }
                let k = spos.len();
                if k < 2 { continue; }
                let m = k - 1;
                let mut jL = match spos.binary_search_by(|v| v.partial_cmp(&sL).unwrap()) {
                    Ok(idx) => idx,
                    Err(idx) => if idx==0 { 0 } else { idx-1 },
                };
                let mut jR = match spos.binary_search_by(|v| v.partial_cmp(&sR).unwrap()) {
                    Ok(idx) => idx,
                    Err(idx) => if idx==0 { 0 } else { idx-1 },
                };
                if jL >= m { jL = m-1; }
                if jR >= m { jR = m-1; }
                let mut best = INF;
                if jL == jR {
                    let edge_start = spos[jL];
                    let mut pL = sL - edge_start; if pL < 0.0 { pL = 0.0; }
                    let mut pR = sR - edge_start;
                    let Lseg = seg.edge_len[jL];
                    if pR > Lseg { pR = Lseg; }
                    let u = seg.nodes[jL]; let v = seg.nodes[jL+1];
                    let du = dist[u]; let dv = dist[v];
                    if du < INF || dv < INF {
                        let val = best_on_edge_intervalue(du, dv, Lseg, pL, pR);
                        if val < best { best = val; }
                    }
                } else {
                    // left part
                    let j = jL;
                    let edge_start = spos[j];
                    let mut pL = sL - edge_start; if pL < 0.0 { pL = 0.0; }
                    let Lseg = seg.edge_len[j];
                    let mut pR = spos[j+1] - edge_start;
                    if pR > Lseg { pR = Lseg; }
                    let u = seg.nodes[j]; let v = seg.nodes[j+1];
                    let du = dist[u]; let dv = dist[v];
                    if du < INF || dv < INF {
                        let val = best_on_edge_intervalue(du, dv, Lseg, pL, pR);
                        if val < best { best = val; }
                    }
                    // right part
                    let j = jR;
                    let edge_start = spos[j];
                    let Lseg = seg.edge_len[j];
                    let pL2 = 0.0;
                    let mut pR2 = sR - edge_start;
                    if pR2 > Lseg { pR2 = Lseg; }
                    if pR2 < 0.0 { pR2 = 0.0; }
                    let u = seg.nodes[j]; let v = seg.nodes[j+1];
                    let du = dist[u]; let dv = dist[v];
                    if du < INF || dv < INF {
                        let val = best_on_edge_intervalue(du, dv, Lseg, pL2, pR2);
                        if val < best { best = val; }
                    }
                    // middle edges by segtree
                    if jL + 1 <= jR - 1 {
                        let l = jL + 1;
                        let r = jR;
                        if seg.st_n > 0 {
                            let val = seg_range_min(&seg.st_seg, seg.st_n, l, r);
                            if val < best { best = val; }
                        }
                    }
                }
                if best < result { result = best; }
            }
            if result >= INF {
                out.push_str("-1\n");
            } else {
                out.push_str(&format!("{:.20}\n", result));
            }
        }
    }
    let stdout = io::stdout();
    let mut handle = stdout.lock();
    handle.write_all(out.as_bytes()).unwrap();
}
