//! Proposal 073 §2 — a value of an abstract type at run time.
//!
//! A value typed at a sort with no constructors of its own that other sorts provide (`Stream`,
//! `Mergeable`) is a pair: the dictionary of the instance it is and the value of the sort that
//! built it, `Instance(dict, value)` (`anthill.realization.runtime.Instance`), an ordinary
//! first-order value as a `Dictionary` is. Which values are pairs is decided by their static
//! type, at load; the typer stamps where a value becomes one ([`InstanceConversion`]), and a
//! call on one enters the member its dictionary names. Nothing here reads a value to choose a
//! dictionary: a pair carries the one fixed where it was made.

use crate::intern::Symbol;
use crate::kb::node_occurrence::materialize_from_handle;
use crate::kb::term::TermId;
use crate::kb::typing::{FieldConversion, InstanceConversion};

use super::error::EvalError;
use super::value::{Dictionary, Value};
use super::Interpreter;
use smallvec::SmallVec;

impl Interpreter {
    /// The pair of `dict` and `value`.
    pub(crate) fn make_instance(&self, dict: Dictionary, value: Value) -> Result<Value, EvalError> {
        // A value is the instance of one sort that built it: pairing a pair again would make the
        // dictionary of the outer one answer for a value that is not its carrier's.
        if self.open_instance(&value).is_some() {
            let running = self
                .stack
                .top()
                .map(|f| self.kb.qualified_name_of(f.op).to_string())
                .unwrap_or_default();
            return Err(EvalError::Internal(format!(
                "a value that is an instance already is paired again with `{}`'s dictionary \
                 (running `{running}`)",
                self.kb.qualified_name_of(dict.impl_sort()),
            )));
        }
        let functor = self.fields.instance.ok_or_else(|| {
            EvalError::Internal(
                "a value of an abstract type needs `anthill.realization.runtime.Instance`, \
                 which this knowledge base never loaded"
                    .into(),
            )
        })?;
        Ok(Value::Entity {
            functor,
            pos: vec![dict.into_value(), value].into(),
            named: Vec::new().into(),
        })
    }

    /// The dictionary and the carrier's value of a pair; `None` for any other value. Read
    /// through the view, so a pair that crossed into the resolver and back — an occurrence,
    /// a term — opens as the entity does.
    pub(crate) fn open_instance(&self, v: &Value) -> Option<(Dictionary, Value)> {
        use crate::kb::term_view::{TermView, ViewHead};
        let functor = self.fields.instance?;
        match v.head(&self.kb) {
            ViewHead::Functor {
                functor: f,
                pos_arity: 2,
                named_arity: 0,
            } if f == functor => {
                let dict_item = v.pos_arg(&self.kb, 0)?.to_value();
                let dict = Dictionary::from_view(&self.kb, &dict_item)?;
                let value = v.pos_arg(&self.kb, 1)?.to_value();
                Some((dict, value))
            }
            _ => None,
        }
    }

    /// [`Self::open_instance`] for a value the typer says is a pair: anything else is a
    /// value an abstract type was given without its instance, which no step may repair.
    pub(crate) fn expect_instance(
        &self,
        v: &Value,
        at: Symbol,
    ) -> Result<(Dictionary, Value), EvalError> {
        // In the resolver's bridge the arguments come from the rule world, which holds no
        // instances; the entry pairs those it can (`pair_host_arguments`), and one it cannot is
        // a symbolic expression a guard is asked about — reading it waits, as an unknown does.
        if self.bridge_mode() && self.open_instance(v).is_none() {
            return Err(self.reads_unknown(&format!(
                "a value at `{}` that is no instance",
                self.kb.qualified_name_of(at)
            )));
        }
        self.open_instance(v).ok_or_else(|| {
            let running = self
                .stack
                .top()
                .map(|f| self.kb.qualified_name_of(f.op).to_string())
                .unwrap_or_default();
            EvalError::Internal(format!(
                "a value at the abstract type `{}` holds no instance (got {}, running `{running}`): \
                 the place that made it did not pair it with its dictionary",
                self.kb.qualified_name_of(at),
                v.type_name(),
            ))
        })
    }

    /// Apply `conv` to `v`. A `Pack`'s dictionary expression is evaluated in the frame on top
    /// of the stack, the one the stamped node runs in; `receiver` is the dictionary of the
    /// instance a call was made on, for [`InstanceConversion::PackAtReceiver`].
    pub(crate) fn apply_instance_conversion(
        &mut self,
        conv: &InstanceConversion,
        v: Value,
        receiver: Option<&Dictionary>,
    ) -> Result<Value, EvalError> {
        match conv {
            InstanceConversion::Pack { dict } => {
                let occ = materialize_from_handle(&self.kb, *dict);
                let dict = self.eval_requirement_chain_node(&occ)?;
                self.pack(dict, v)
            }
            InstanceConversion::PackAtReceiver => {
                let dict = receiver.cloned().ok_or_else(|| {
                    EvalError::Internal(
                        "a result typed at the instance a call was made on, reached with no \
                         instance"
                            .into(),
                    )
                })?;
                self.pack(dict, v)
            }
            InstanceConversion::Fields { ctors, .. } => {
                self.convert_fields(conv, ctors, v, receiver)
            }
            InstanceConversion::Tuple { components } => self.convert_tuple(components, v, receiver),
            InstanceConversion::Function { result } => {
                self.convert_function_result(result, v, receiver)
            }
            // Read in place of the node ([`Self::built_dictionary_value`]); a value it
            // converted would be the call's own, which nothing makes.
            InstanceConversion::BuiltDictionary { .. } => Err(EvalError::Internal(
                "a `Dictionary.instance` call's dictionary applied to a value: it is read in \
                 place of the node it is stamped on"
                    .into(),
            )),
        }
    }

    /// Proposal 074 §2 — the value of a `Dictionary.instance[S]()` call: the dictionary `dict`
    /// evaluates to in the frame on top of the stack, the node's own.
    pub(crate) fn built_dictionary_value(&mut self, dict: TermId) -> Result<Value, EvalError> {
        let occ = materialize_from_handle(&self.kb, dict);
        Ok(self.eval_requirement_chain_node(&occ)?.as_value().clone())
    }

    /// [`Self::pack`], for a dispatch that pairs an argument with the dictionary it came
    /// through.
    pub(crate) fn pair_with(&self, dict: Dictionary, v: Value) -> Result<Value, EvalError> {
        self.pack(dict, v)
    }

    /// Pair `v` with `dict` — unless `dict` is the abstract sort's own stand-in, whose
    /// values are pairs already: a value typed at the abstract sort is one, and the
    /// instance it holds is the one it was made with.
    fn pack(&self, dict: Dictionary, v: Value) -> Result<Value, EvalError> {
        if crate::kb::typing::is_abstract_carrier_sort(&self.kb, dict.impl_sort()) {
            self.expect_instance(&v, dict.impl_sort())?;
            return Ok(v);
        }
        self.make_instance(dict, v)
    }

    /// A closure whose result is converted where it is applied: a copy of it carrying the
    /// conversion ([`super::closure::Closure::result_conversion`]).
    fn convert_function_result(
        &mut self,
        result: &InstanceConversion,
        v: Value,
        receiver: Option<&Dictionary>,
    ) -> Result<Value, EvalError> {
        let Value::Closure(handle) = &v else {
            return Err(EvalError::Internal(format!(
                "a function value whose result is an instance where it is used is a {}: only \
                 a lambda's closure carries the conversion of its result",
                v.type_name()
            )));
        };
        let copy = handle.with(|c| {
            if c.result_conversion.is_some() {
                return Err(EvalError::Internal(
                    "a closure's result converted again where it is used".into(),
                ));
            }
            Ok(super::closure::Closure {
                param_pattern: c.param_pattern.clone(),
                body: c.body.clone(),
                env: SmallVec::new(),
                requirements: c.requirements.clone(),
                written_in: c.written_in,
                relabel: c.relabel.clone(),
                result_conversion: Some((result.clone(), receiver.cloned())),
                instance_binders: c.instance_binders.clone(),
            })
        })?;
        let env = handle.clone_env();
        let copy = super::closure::Closure { env, ..copy };
        Ok(Value::Closure(self.closures.alloc(copy)))
    }

    fn convert_tuple(
        &mut self,
        components: &[(Symbol, InstanceConversion)],
        v: Value,
        receiver: Option<&Dictionary>,
    ) -> Result<Value, EvalError> {
        let Value::Tuple { pos, named } = &v else {
            return Err(EvalError::Internal(format!(
                "a value converted through its tuple components is no tuple (got {})",
                v.type_name()
            )));
        };
        let mut pos: Vec<Value> = pos.to_vec();
        let mut named: Vec<(Symbol, Value)> = named.to_vec();
        for (label, conv) in components {
            if let Some(slot) = named.iter_mut().find(|(n, _)| n == label) {
                let taken = std::mem::replace(&mut slot.1, Value::Unit);
                slot.1 = self.apply_instance_conversion(conv, taken, receiver)?;
                continue;
            }
            let index = crate::intern::positional_label_index(self.kb.local_name_of(*label))
                .filter(|&i| i < pos.len())
                .ok_or_else(|| {
                    EvalError::Internal(format!(
                        "tuple component `{}` to convert is not in the value",
                        self.kb.local_name_of(*label)
                    ))
                })?;
            let taken = std::mem::replace(&mut pos[index], Value::Unit);
            pos[index] = self.apply_instance_conversion(conv, taken, receiver)?;
        }
        Ok(Value::Tuple {
            pos: pos.into(),
            named: named.into(),
        })
    }

    fn convert_fields(
        &mut self,
        whole: &InstanceConversion,
        ctors: &[(Symbol, Vec<(Symbol, FieldConversion)>)],
        v: Value,
        receiver: Option<&Dictionary>,
    ) -> Result<Value, EvalError> {
        let Value::Entity {
            functor,
            pos,
            named,
        } = &v
        else {
            return Err(EvalError::Internal(format!(
                "a value converted through its constructor's fields is no constructed value \
                 (got {})",
                v.type_name()
            )));
        };
        let Some((_, fields)) = ctors.iter().find(|(c, _)| c == functor) else {
            // A constructor none of whose fields is converted (`none`, `nil`).
            return Ok(v);
        };
        let names = self.kb.entity_field_names(*functor).map(|n| n.to_vec());
        let mut pos: Vec<Value> = pos.to_vec();
        let mut named: Vec<(Symbol, Value)> = named.to_vec();
        for (field, fc) in fields {
            let inner: &InstanceConversion = match fc {
                FieldConversion::Param(c) => c,
                FieldConversion::Recur => whole,
            };
            if let Some(slot) = named.iter_mut().find(|(n, _)| n == field) {
                let taken = std::mem::replace(&mut slot.1, Value::Unit);
                slot.1 = self.apply_instance_conversion(inner, taken, receiver)?;
                continue;
            }
            let index = names
                .as_ref()
                .and_then(|n| n.iter().position(|f| f == field))
                .filter(|&i| i < pos.len())
                .ok_or_else(|| {
                    EvalError::Internal(format!(
                        "field `{}` of `{}` to convert is not in the value",
                        self.kb.local_name_of(*field),
                        self.kb.qualified_name_of(*functor),
                    ))
                })?;
            let taken = std::mem::replace(&mut pos[index], Value::Unit);
            pos[index] = self.apply_instance_conversion(inner, taken, receiver)?;
        }
        Ok(Value::Entity {
            functor: *functor,
            pos: pos.into(),
            named: named.into(),
        })
    }
}
