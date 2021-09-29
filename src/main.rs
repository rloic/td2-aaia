use std::ops::{Add, Sub, SubAssign, Index, IndexMut};
use std::fmt::{Debug, Formatter};
use std::fmt;
use std::time::Instant;
use std::io::{stdin, stdout, Write};
use std::collections::HashMap;

type Node = usize;
type Cost = i32;

fn main() -> std::io::Result<()> {
    print!("Nombre de sommets : ");
    stdout().flush()?;

    let mut line = String::new();
    stdin().read_line(&mut line)?;
    let nb_nodes = line.trim().parse()
        .expect("Impossible de lire le nombre de sommets");

    let costs = create_costs(nb_nodes);

    /*
        let clock = Instant::now();
        let mut nb_call = -1;
        let distance = compute_distance(0, Set::filled(nb_nodes), nb_nodes, &costs, &mut nb_call);

        println!("Longueur du plus court circuit hamiltonien = {}; temps de calcul = {:.3}s", distance, clock.elapsed().as_secs_f32());
        println!("Number of recursive call: {}", nb_call);
    */

    let mut mem = vec![vec![None; 1 << (nb_nodes - 1)]; nb_nodes];
    let clock = Instant::now();
    let distance = compute_distance_mem(0, Set::filled(nb_nodes), nb_nodes, &costs, &mut mem);

    println!("Longueur du plus court circuit hamiltonien = {}; temps de calcul = {:.3}s", distance, clock.elapsed().as_secs_f32());

    let clock = Instant::now();
    let distance = compute_iter(&costs, Set::filled(nb_nodes), nb_nodes);
    println!("Longueur du plus court circuit hamiltonien = {}; temps de calcul = {:.3}s", distance, clock.elapsed().as_secs_f32());

    compute_iter_show_path(&costs, Set::filled(nb_nodes), nb_nodes);

    Ok(())
}

fn compute_distance(i: Node, s: Set, n: usize, cost: &Vec<Vec<Cost>>, nb_call: &mut i32) -> Cost {
    *nb_call += 1;
    if s.is_empty() { cost[i][0] } else {
        let mut min = Cost::MAX;
        for j in s {
            let distance = compute_distance(j, s - j, n, cost, nb_call);
            if cost[i][j] + distance < min {
                min = cost[i][j] + distance;
            }
        }
        min
    }
}

fn compute_distance_mem(i: Node, s: Set, nb_nodes: usize, cost: &Vec<Vec<Cost>>, mem: &mut Vec<Vec<Option<Cost>>>) -> Cost {
    if let Some(distance) = mem[i][s] {
        distance
    } else {
        let distance = if s.is_empty() { cost[i][0] } else {
            let mut min = Cost::MAX;
            for j in s {
                let distance = compute_distance_mem(j, s - j, nb_nodes, cost, mem);
                if cost[i][j] + distance < min {
                    min = cost[i][j] + distance;
                }
            }
            mem[i][s] = Some(min);
            min
        };
        distance
    }
}

fn compute_iter(cost: &Vec<Vec<Cost>>, s: Set, nb_nodes: usize) -> Cost {
    let mut mem_d = vec![vec![0; 1 << (nb_nodes - 1)]; nb_nodes];

    for e in 0..1 << (nb_nodes - 1) {
        let e = Set(e);
        for i in s - e {
            if e.is_empty() {
                mem_d[i][e] = cost[i][0];
            } else {
                mem_d[i][e] = Cost::MAX;
                for j in e {
                    if cost[i][j] + mem_d[j][(e - j)] < mem_d[i][e] {
                        mem_d[i][e] = cost[i][j] + mem_d[j][(e - j)];
                    }
                }
            }
        }
    }

    mem_d[0][s] = Cost::MAX;
    for j in s {
        if cost[0][j] + mem_d[j][(s - j)] < mem_d[0][s] {
            mem_d[0][s] = cost[0][j] + mem_d[j][(s - j)];
        }
    }

    mem_d[0][s]
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
struct NodeAndSet { node: Node, set: Set }

impl NodeAndSet {
    fn new(node: usize, set: Set) -> NodeAndSet {
        NodeAndSet { node, set }
    }
}

struct Edge { from: Node, to: Node }

impl Edge {
    fn new(from: usize, to: usize) -> Edge {
        Edge { from, to }
    }
}

fn compute_iter_show_path(cost: &Vec<Vec<Cost>>, s: Set, nb_nodes: usize) -> Cost {
    let mut mem_d = vec![vec![0; 1 << (nb_nodes - 1)]; nb_nodes];

    let mut parent = HashMap::new();

    for e in 0..1 << (nb_nodes - 1) {
        let e = Set(e);
        for i in s - e {
            if e.is_empty() {
                mem_d[i][e] = cost[i][0];
            } else {
                mem_d[i][e] = Cost::MAX;
                for j in e {
                    if cost[i][j] + mem_d[j][(e - j)] < mem_d[i][e] {
                        mem_d[i][e] = cost[i][j] + mem_d[j][(e - j)];
                        parent.insert(NodeAndSet::new(i, e), Edge::new(j, i));
                    }
                }
            }
        }
    }

    mem_d[0][s] = Cost::MAX;
    for j in s {
        if cost[0][j] + mem_d[j][(s - j)] < mem_d[0][s] {
            mem_d[0][s] = cost[0][j] + mem_d[j][(s - j)];
            parent.insert(NodeAndSet::new(0, s), Edge::new(j, 0));
        }
    }

    let mut curr = NodeAndSet::new(0, s);
    let mut dist = 0;
    while let Some(p) = parent.get(&curr) {
        dist += cost[curr.node][p.from];
        println!("{} -> {} ({})", curr.node, p.from, cost[curr.node][p.from]);
        curr = NodeAndSet::new(p.from, curr.set - p.from);
    }

    dist += cost[curr.node][0];
    println!("{} -> {} ({})", curr.node, 0, cost[curr.node][0]);
    println!("{}", dist);

    mem_d[0][s]
}

fn next_rand(seed: Cost) -> Cost {
    let i = 16807 * (seed % 127773) - 2836 * (seed / 127773);
    if i > 0 { i } else { 2147483647 + i }
}

fn create_costs(nb_elements: usize) -> Vec<Vec<Cost>> {
    let max_cost = 1000;
    let mut iseed = 1;
    let mut cost = Vec::with_capacity(nb_elements);
    for i in 0..nb_elements {
        cost.push(Vec::with_capacity(nb_elements));
        for j in 0..nb_elements {
            if i == j {
                cost[i].push(max_cost + 1);
            } else {
                iseed = next_rand(iseed);
                cost[i].push(1 + iseed % max_cost);
            }
        }
    }

    cost
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
struct Set(usize);

impl Set {
    fn filled(capacity: usize) -> Set {
        Set((1 << (capacity - 1)) - 1)
    }

    fn is_empty(&self) -> bool {
        self.0 == 0
    }

    fn lowest_element(&self) -> Option<Node> {
        if self.is_empty() {
            None
        } else {
            Some(self.0.trailing_zeros() as usize + 1)
        }
    }
}

impl Add<Node> for Set {
    type Output = Set;

    fn add(self, rhs: Node) -> Self::Output {
        Set(self.0 | (1 << rhs - 1))
    }
}

impl Sub<Set> for Set {
    type Output = Set;

    fn sub(self, rhs: Set) -> Self::Output {
        Set(self.0 & !rhs.0)
    }
}

impl Sub<Node> for Set {
    type Output = Set;

    fn sub(self, rhs: Node) -> Self::Output {
        Set(self.0 & !(1 << rhs - 1))
    }
}

impl SubAssign<Node> for Set {
    fn sub_assign(&mut self, rhs: Node) {
        self.0 &= !(1 << rhs - 1)
    }
}

impl Debug for Set {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut s = self.0;

        let mut i = 1;
        while s != 0 {
            if s & 1 != 0 {
                write!(f, " {}", i)?;
            }
            s = s >> 1;
            i += 1;
        }

        Ok(())
    }
}

impl<T> Index<Set> for Vec<T> {
    type Output = T;

    fn index(&self, index: Set) -> &Self::Output {
        &self[index.0]
    }
}

impl<T> IndexMut<Set> for Vec<T> {
    fn index_mut(&mut self, index: Set) -> &mut Self::Output {
        &mut self[index.0]
    }
}

impl IntoIterator for Set {
    type Item = Node;
    type IntoIter = SetIterator;

    fn into_iter(self) -> Self::IntoIter {
        SetIterator { inner: self }
    }
}

struct SetIterator {
    inner: Set,
}

impl Iterator for SetIterator {
    type Item = Node;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(next) = self.inner.lowest_element() {
            self.inner -= next;
            Some(next)
        } else {
            None
        }
    }
}