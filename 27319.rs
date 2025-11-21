use std::io::{self, Read};

#[derive(Clone, Copy)]
struct P { x: i128, y: i128 }
fn cross(a: P, b: P) -> i128 { a.x*b.y - a.y*b.x }
fn sub(a: P, b: P) -> P { P { x: a.x-b.x, y: a.y-b.y } }
fn add(a: P, b: P) -> P { P { x: a.x+b.x, y: a.y+b.y } }
fn dot(a: P, b: P) -> i128 { a.x*b.x + a.y*b.y }

fn signed_area(a: &[P]) -> i128 {
    let n = a.len();
    let mut s: i128 = 0;
    for i in 0..n {
        let j = (i+1)%n;
        s += a[i].x * a[j].y - a[i].y * a[j].x;
    }
    s
}

fn is_convex_vertex(p: &Vec<P>, idx: usize, orient_sign: i128) -> bool {
    let n = p.len();
    let prev = (idx + n - 1) % n;
    let next = (idx + 1) % n;
    let v1 = sub(p[idx], p[prev]);
    let v2 = sub(p[next], p[idx]);
    let cr = cross(v1, v2);
    cr * orient_sign > 0
}

fn is_reflex_vertex(p: &Vec<P>, idx: usize, orient_sign: i128) -> bool {
    let n = p.len();
    let prev = (idx + n - 1) % n;
    let next = (idx + 1) % n;
    let v1 = sub(p[idx], p[prev]);
    let v2 = sub(p[next], p[idx]);
    let cr = cross(v1, v2);
    cr * orient_sign < 0
}

fn collect_chain(p: &Vec<P>, a: usize, b: usize) -> Vec<P> {
    let n = p.len();
    let mut v = Vec::new();
    let mut i = a;
    loop {
        v.push(p[i]);
        if i == b { break; }
        i = (i + 1) % n;
    }
    v
}

fn is_convex_polygon_chain(chain: &Vec<P>) -> bool {
    let m = chain.len();
    if m < 3 { return true; }
    let s = signed_area(chain);
    if s == 0 { return false; }
    let orient = if s > 0 { 1 } else { -1 };
    for i in 0..m {
        let prev = (i + m - 1) % m;
        let next = (i + 1) % m;
        let v1 = sub(chain[i], chain[prev]);
        let v2 = sub(chain[next], chain[i]);
        let cr = cross(v1, v2);
        if cr == 0 { return false; }
        if cr * (orient as i128) <= 0 { return false; }
    }
    true
}

fn main() {
    let mut s = String::new();
    io::stdin().read_to_string(&mut s).unwrap();
    let mut it = s.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut p: Vec<P> = Vec::with_capacity(n);
    for _ in 0..n {
        let x: i128 = it.next().unwrap().parse::<i128>().unwrap();
        let y: i128 = it.next().unwrap().parse::<i128>().unwrap();
        p.push(P { x, y });
    }

    if n % 2 == 1 {
        println!("0");
        return;
    }

    let area = signed_area(&p);
    if area == 0 {
        println!("0");
        return;
    }
    let orient_sign = if area > 0 { 1 } else { -1 };

    let half = n/2;
    for a in 0..n {
        let b = (a + half) % n;
        if !is_convex_vertex(&p, a, orient_sign) { continue; }
        if !is_reflex_vertex(&p, b, orient_sign) { continue; }

        let v = sub(p[b], p[a]);
        let mut ok = true;
        for t in 0..=half {
            let u_idx = (a + t) % n;
            let v_idx = (a + n - t) % n;
            let sum = add(p[u_idx], p[v_idx]);
            let lhs = sub(sum, P { x: 2*p[a].x, y: 2*p[a].y });
            if cross(v, lhs) != 0 {
                ok = false;
                break;
            }
            let diff = sub(p[v_idx], p[u_idx]);
            if dot(v, diff) != 0 {
                ok = false;
                break;
            }
        }
        if !ok { continue; }

        let chain1 = collect_chain(&p, a, b);
        let chain2 = collect_chain(&p, b, a);
        if is_convex_polygon_chain(&chain1) && is_convex_polygon_chain(&chain2) {
            println!("1");
            return;
        }
    }

    println!("0");
}
