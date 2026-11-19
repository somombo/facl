use crate::syntax::{Allow, Block, Item, SPAN};
use crate::wire::Case;
use facl_core::{Expr, ExprKind as E};

pub(crate) fn shrink<T>(
    mut case: Case,
    mut keep: impl FnMut(&Case) -> Result<bool, T>,
) -> Result<Case, T> {
    'search: loop {
        for requests in edit_list(&case.requests, |_| Vec::new()) {
            let candidate = Case {
                requests,
                ..case.clone()
            };
            if keep(&candidate)? {
                case = candidate;
                continue 'search;
            }
        }
        for blocks in edit_list(&case.policy.blocks, edit_block) {
            let mut candidate = case.clone();
            candidate.policy.blocks = blocks;
            if keep(&candidate)? {
                case = candidate;
                continue 'search;
            }
        }
        return Ok(case);
    }
}

fn edit_list<T: Clone>(values: &[T], replacements: impl Fn(&T) -> Vec<T>) -> Vec<Vec<T>> {
    let mut candidates = Vec::new();
    for i in 0..values.len() {
        let mut candidate = values.to_vec();
        candidate.remove(i);
        candidates.push(candidate);
    }
    for (i, value) in values.iter().enumerate() {
        for replacement in replacements(value) {
            let mut candidate = values.to_vec();
            candidate[i] = replacement;
            candidates.push(candidate);
        }
    }
    candidates
}

fn edit_block(block: &Block) -> Vec<Block> {
    edit_list(&block.body, edit_item)
        .into_iter()
        .map(|body| Block {
            body,
            ..block.clone()
        })
        .collect()
}

fn edit_item(item: &Item) -> Vec<Item> {
    match item {
        Item::Match(block) => edit_block(block).into_iter().map(Item::Match).collect(),
        Item::Allow(allow) => {
            let mut candidates = Vec::new();
            if allow.actions.len() > 1 {
                candidates.extend(edit_list(&allow.actions, |_| Vec::new()).into_iter().map(
                    |actions| {
                        Item::Allow(Allow {
                            actions,
                            ..allow.clone()
                        })
                    },
                ));
            }
            if let Some(cond) = &allow.cond {
                candidates.push(Item::Allow(Allow {
                    cond: None,
                    ..allow.clone()
                }));
                candidates.extend(edit_expr(cond).into_iter().map(|expr| {
                    Item::Allow(Allow {
                        cond: Some(expr),
                        ..allow.clone()
                    })
                }));
            }
            candidates
        }
    }
}

fn edit_expr(expr: &Expr) -> Vec<Expr> {
    let mut candidates = match expr.kind {
        E::Null | E::Bool(_) => return Vec::new(),
        _ => vec![node(E::Null), node(E::Bool(false)), node(E::Bool(true))],
    };
    match &expr.kind {
        E::Not(arg) => edit_child(&mut candidates, arg, E::Not),
        E::Select(target, key) => {
            edit_child(&mut candidates, target, |edited| {
                E::Select(edited, key.clone())
            });
        }
        E::Index(l, r) => edit_pair(&mut candidates, l, r, E::Index),
        E::And(l, r) => edit_pair(&mut candidates, l, r, E::And),
        E::Or(l, r) => edit_pair(&mut candidates, l, r, E::Or),
        E::In(l, r) => edit_pair(&mut candidates, l, r, E::In),
        E::Cmp(op, l, r) => {
            edit_pair(&mut candidates, l, r, |a, b| E::Cmp(op.clone(), a, b));
        }
        E::List(args) => {
            candidates.extend(args.iter().cloned());
            candidates.extend(
                edit_list(args, edit_expr)
                    .into_iter()
                    .map(|args| node(E::List(args))),
            );
        }
        E::Call(name, args) => {
            candidates.extend(args.iter().cloned());
            candidates.extend(
                edit_list(args, edit_expr)
                    .into_iter()
                    .map(|args| node(E::Call(name.clone(), args))),
            );
        }
        E::Method(target, name, args) => {
            edit_child(&mut candidates, target, |edited| {
                E::Method(edited, name.clone(), args.clone())
            });
            candidates.extend(args.iter().cloned());
            candidates.extend(
                edit_list(args, edit_expr)
                    .into_iter()
                    .map(|args| node(E::Method(target.clone(), name.clone(), args))),
            );
        }
        E::Int(n) if *n != 0 => candidates.push(node(E::Int(0))),
        E::Str(s) if !s.is_empty() => candidates.push(node(E::Str(Vec::new()))),
        _ => {}
    }
    candidates
}

fn edit_child(candidates: &mut Vec<Expr>, child: &Expr, replace: impl Fn(Box<Expr>) -> E) {
    candidates.push(child.clone());
    candidates.extend(
        edit_expr(child)
            .into_iter()
            .map(|expr| node(replace(Box::new(expr)))),
    );
}

fn edit_pair(
    candidates: &mut Vec<Expr>,
    l: &Expr,
    r: &Expr,
    replace: impl Fn(Box<Expr>, Box<Expr>) -> E,
) {
    edit_child(candidates, l, |edited| replace(edited, Box::new(r.clone())));
    edit_child(candidates, r, |edited| replace(Box::new(l.clone()), edited));
}

fn node(kind: E) -> Expr {
    Expr { kind, span: SPAN }
}
