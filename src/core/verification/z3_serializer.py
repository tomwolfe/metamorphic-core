# src/core/verification/z3_serializer.py
from z3 import *
import json

class Z3JSONEncoder(json.JSONEncoder):
    def default(self, obj):
        if isinstance(obj, ModelRef):
            return self.serialize_z3_model(obj)
        return super().default(obj)

    def serialize_z3_model(self, model):
        return {
            decl.name(): self._z3_value_to_python(model[decl])
            for decl in model.decls()
        }

    def _z3_value_to_python(self, value):
        if is_rational_value(value):
            return float(value.as_fraction())
        if is_algebraic_value(value):
            return str(value.approx(5))
        if is_true(value) or is_false(value):
            return bool(value)
        return str(value)
