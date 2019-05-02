import sys, copy
from enum import Enum

sys.path.extend(['pycparser'])

from pycparser import parse_file, c_parser, c_ast

filecontent = None

class State(Enum):
    UNOWNED = 0
    # moved or free; the 'zombie' name is from the POM paper
    ZOMBIE = 1
    # Owned and valid
    OWNED = 2
    # possibly owned or zombie; the union of both, for when we unify states.
    UNKNOWN = 3
    # Not initialized.
    UNINIT = 4
    # Possibly initialized?
    MAYBEINIT = 5

class TypeCheckError(Exception):
    def __init__(self, location, msg):
        super().__init__(msg)
        self.line = location.line
        self.column = location.column
        self.location = (
            location.file
                + ", line " + str(location.line)
                + " column " + str(location.column)
        )


class NamedType:
    """ A type that just has a name.
        Includes int, char, etc. and also typedefs.
        Also the names are a list of strings because
        we have stuff like 'unsigned int'. This basically
        comes straight from pycparser. """
    def __init__(self, names, quals):
        self.names = names
        for name in names:
            if name not in { "unsigned", "signed", "long", "short",
                             "int", "float", "double", "char", "void" }:
                self.is_typedef = True
                break
        else:
            self.is_typedef = False
        self.quals = quals

    def __str__(self):
        return " ".join(self.names)


class StructType:
    """ A struct type.
        Has a list of fields, which are represented as
        a list of tuples of names and types. """
    def __init__(self, name, fields, field_order, quals):
        if name is not None:
            self.name = name
        else:
            self.name = '<anonymous>'
        self.fields = fields
        self.field_order = field_order
        self.quals = quals

    def __str__(self):
        return 'struct ' + self.name


class PointerType:
    """ A pointer to another type.
        ptrto = what it's a pointer to
        quals = list of qualifiers (const, etc) """
    def __init__(self, ptrto, quals):
        self.ptrto = ptrto
        self.quals = quals

    def __str__(self):
        return str(self.ptrto) + "*" + "".join([" " + x for x in self.quals])


malloc_return_type = PointerType(NamedType(["void"], []), ["@owned"])


def is_ptr(t, info=None):
    """ Returns whether or not a type is a pointer. """
    if info is None:
        return type(t) == PointerType

    if type(unwrap_type(t, info)) == PointerType:
        return True
    else:
        return False


def is_owned_ptr(t, info=None):
    """ Returns whether or not a type is an OWNED pointer.
        (This is necessary because t might be a typedef
        that has '@owned' in its own qualifications, but not
        in the qualifications of the actual pointer type.)
        (They might be at different nested typedefs, for example.)
        Also, the '@frees' qualifier marks that a function frees
        its parameter, rather than passing it off somewhere. """

    if info is None:
        return type(t) == PointerType and ('@owned' in t.quals or '@frees' in t.quals)

    return is_ptr(t, info) and (
        '@owned' in unwrap_type(t, info).quals or '@frees' in unwrap_type(t, info).quals
    )


def get_final_state(t, info=None):
    """ For a given type that a function parameter might
        have, return the type we want it to have when we
        leave a function. (If the parameter has '@frees',
        we want it to be freed; if it has '@owned', we
        want it to be unowned; otherwise, it's not an owned
        pointer, so we want it to be unowned. """
    if is_ptr(t, info):
        if is_owned_ptr(t, info):
            if '@frees' in unwrap_type(t, info).quals:
                return State.ZOMBIE
            elif '@owned' in unwrap_type(t, info).quals:
                return State.UNOWNED
        else:
            return State.UNOWNED
    else:
        return None


def is_unowned_ptr(t, info=None):
    return is_ptr(t, info) and not is_owned_ptr(t, info)


def convert_type(node, info):
    """ Convert a c_ast type node to a Type object. """
    def recurse(node, info, quals):
        t = type(node)

        if t == c_ast.PtrDecl:
            return PointerType(recurse(node.type, info, []), quals + node.quals)
        elif t == c_ast.ArrayDecl:
            return PointerType(recurse(node.type, info, []), quals)
        elif t == c_ast.TypeDecl:
            return recurse(node.type, info, quals + node.quals)
        elif t == c_ast.IdentifierType:
            return NamedType(node.names, quals)
        elif t == c_ast.Struct:
            if node.decls is not None:
                # Declaring struct type
                # (If we don't hit this if-branch, we're declaring a variable
                #  with the struct type instead.)
                # NOTE: this will likely fail if we have like 'struct X;'
                # alone on its own line.
                # This is a shortcut I'm willing to take, for now.
                fields = {}
                field_order = []
                for decl in node.decls:
                    name = decl.name
                    tp = get_type(decl, {}, info)
                    fields[name] = tp
                    field_order.append(name)
                    info['structs'][node.name] = StructType(node.name, fields, field_order, quals)
            return info['structs'][node.name]
        else:
            raise TypeCheckError(node.coord, "Don't know how to convert type " + str(t))

    return recurse(node, info, [])


def assignment_okay(var, expr, info):
    """ Check whether something of type `expr` can be assigned
        to something of type `var`. """
    var = unwrap_type(var, info)
    expr = unwrap_type(expr, info)
    if "const" in var.quals:
        # can't reassign const variables
        return False, "Can't reassign a const variable."

    return initialization_okay(var, expr, info)


def initialization_okay(var, expr, info):
    """ Same as assignment_okay, except that it's okay to assign
        to things that are const because we're initializing. """
    var = unwrap_type(var, info)
    expr = unwrap_type(expr, info)

    if is_ptr(var, info) and expr == malloc_return_type:
        # Allow malloc return values to be converted to any pointer type.
        # This kinda sucks, because we can't be sure it's the right thing,
        # but there's not much we can do here because of how C works.
        return True, ""

    if is_ptr(var, info) and not is_ptr(expr, info):
        return False, "Making pointer from non-pointer without a cast."
    elif not is_ptr(var, info) and is_ptr(expr, info):
        return False, "Assigning pointer to non-pointer variable without a cast."

    if type(var) == NamedType:
        return var.names == expr.names, "Can't convert %s to %s" % (" ".join(expr.names), " ".join(var.names))

    if is_ptr(var, info):
        return initialization_okay(var.ptrto, expr.ptrto, info)

    if type(var) == StructType:
        # NOTE: this fails if we have two different structs with
        # the same name (e.g. in different scopes.) I don't think
        # this is a big issue to solve here, but worth noting that
        # it's not actually correct.
        return var.name == expr.name, "Can't convert struct %s to struct %s" % (expr.name, var.name)

    raise Exception(
        "Don't know how to handle assignment: " + str(var) + " <- " + str(expr)
    )


def unwrap_type(t, info):
    """ Given a type, if it's a typedef, then
        find its actual underlying type.
        (note: will throw KeyError if a typedef refers to
        a nonexistent type. But that should have been an
        error anyway when we encountered the typedef, so
        it's fine.)
        It also keeps track of the qualifiers of the types
        that it encounters along the way, so if A is a
        typedef for B, and we have an A const, unwrapping
        it should yield a B const. """
    def recurse(t, info, extra_quals):
        if t == malloc_return_type:
            return t
        if type(t) == NamedType and t.is_typedef:
            return recurse(info['typedefs'][t.names[0]], info, extra_quals + t.quals)
        else:
            fresh_type = copy.deepcopy(t)
            fresh_type.quals += extra_quals
            return fresh_type
    return recurse(t, info, [])


def unowned_version(owned_ptr, info):
    expansion = unwrap_type(owned_ptr, info)
    while "@owned" in expansion.quals:
        expansion.quals.remove("@owned")
    while "@frees" in expansion.quals:
        expansion.quals.remove("@frees")
    return expansion


def expand_type_name(t, info):
    """ Given a type, print it in a way that exposes all
        typedefs. """
    def recurse(t, info, use_brackets, suffix):
        # This internal function prevents an explosion of brackets
        # for nested typedefs. And lets us put a suffix on the end.
        if use_brackets:
            equals = " [= "
            endbracket = "]"
        else:
            equals = " = "
            endbracket = ""

        if is_typedef(t):
            return (str(t) + suffix + equals
                        + recurse(info['typedefs'][t.names[0]], info, False, " ".join(t.quals) + suffix)
                        + endbracket)
        elif is_ptr(t, info) and is_typedef(t.ptrto):
            if len(t.quals) > 0 or len(suffix) > 0:
                return recurse(t.ptrto, info, use_brackets, "* " + " ".join(t.quals) + suffix)
            else:
                return recurse(t.ptrto, info, use_brackets, "*")
        else:
            return str(t) + suffix

    return recurse(t, info, True, "")


def is_typedef(t):
    """ Return whether or not a given type is a typedef. """
    if type(t) == NamedType:
        return t.is_typedef
    else:
        return False


def show_error(e):
    print(e.location + ":", str(e))
    print(filecontent[e.line - 1])
    print(" " * (e.column - 1) + "^")


node_types = {}
function_types = {}
error_in_typecheck_phase = False

def get_type(node, context, info):
    """ Walks over the pycparser-generated AST.
        Checks that a statement has correct type, and also returns
        types of expressions. """
    global error_in_typecheck_phase

    t = type(node)

    if t == c_ast.FileAST:
        #print(node)
        for decl in node.ext:
            try:
                get_type(decl, context, info)
            except TypeCheckError as e:
                error_in_typecheck_phase = True
                show_error(e)
                continue

    elif t == c_ast.FuncDef:
        info_with_return = copy.deepcopy(info)
        info_with_return['func_return'] = convert_type(node.decl.type.type, info)
        info_with_return['func_name'] = node.decl.name

        # Save the return type of the function.
        node_types[node] = info_with_return['func_return']

        # Use a fresh copy of the context dict, so declarations
        # inside each function don't leak outside it, even if we
        # add things to the context.
        func_context = context.copy()

        # Build the list of function parameters and their types,
        # so we can later check them when a function gets called.
        func_params = []

        if node.decl.type.args is not None:
            for param in node.decl.type.args.params:
                # Put parameters into function scope, by parsing them
                # as declarations.
                param_type = get_type(param, func_context, info_with_return)

                # Also, save what type of parameters are expected by the
                # function so we can check it if it's called later.
                func_params.append((param.name, param_type))

        # Save function return types and argument types.
        function_types[node.decl.name] = (info_with_return['func_return'], func_params)

        get_type(node.body, func_context, info_with_return)

    elif t == c_ast.Compound:
        # As above.
        block_context = context.copy()
        if node.block_items: # (might be an empty block...)
            for stmt in node.block_items:
                try:
                    get_type(stmt, block_context, info)
                except TypeCheckError as e:
                    error_in_typecheck_phase = True
                    show_error(e)
                    continue

    elif t == c_ast.Decl:
        # A declaration. This is where we get the actual types
        # of names that are in scope.
        # Note: We don't really care about anything other than
        # its declared type. Doesn't matter if it's extern, or
        # something -- just assume it's correct.
        tp = convert_type(node.type, info)

        unwrapped_type = unwrap_type(tp, info)
        if is_ptr(unwrapped_type, info):
            if is_owned_ptr(unwrapped_type, info):
                info['states'][node.name] = State.UNINIT
            else:
                info['states'][node.name] = State.UNOWNED

        if node.init != None:
            expr_tp = get_type(node.init, context, info)
            ok, reason = initialization_okay(tp, expr_tp, info)

            if not ok:
                raise TypeCheckError(
                    node.coord, "can't initialize variable " + node.name
                                + " of type " + expand_type_name(tp, info)
                                + " with expression of type " + expand_type_name(expr_tp, info)
                                + ": " + reason
                )

            if is_owned_ptr(unwrapped_type, info):
                # If it's initialized, mark it OWNED
                info['states'][node.name] = State.OWNED

        # Associate the type with the name in context.
        context[node.name] = tp

        node_types[node] = tp

    elif t == c_ast.Typedef:
        if node.name in info['typedefs']:
            print("%s: %d.%d: warning: redefining typedef %s" % (
                node.coord.file, node.coord.line, node.coord.column
            ))
        info['typedefs'][node.name] = convert_type(node.type, info)

    elif t == c_ast.ArrayRef:
        subscript_type = get_type(node.subscript, context, info)
        array_type = get_type(node.name, context, info)

        if type(array_type) != PointerType:
            raise TypeCheckError(
                node.coord, "can't subscript type " + expand_type_name(array_type, info)
                          + ", which isn't a pointer or array"
            )

    elif t == c_ast.StructRef:
        if node.type == "->":
            # a->b
            type_is_ptr = True
            left_type = get_type(node.name, context, info)
            real_left_type = unwrap_type(left_type, info)
            if type(real_left_type) != PointerType:
                # Using -> on a non-pointer.
                raise TypeCheckError(
                    node.coord, "can't use -> access on expression of type "
                                + expand_type_name(left_type, info)
                                + ", which isn't a pointer type"
                )

            struct_type = unwrap_type(real_left_type.ptrto, info)
        else:
            # a.b
            type_is_ptr = False
            left_type = get_type(node.name, context, info)
            real_left_type = struct_type = unwrap_type(left_type, info)

        type_str = expand_type_name(left_type, info)

        if type(struct_type) != StructType:
            if not type_is_ptr:
                # Using . on a non-struct type.
                raise TypeCheckError(
                    node.coord, "request for element '" + node.field.name
                    + "' in expression of type " + type_str
                    + ", which is not a struct or union"
                )
            else:
                # Using -> on a pointer that isn't to a struct.
                raise TypeCheckError(
                    node.coord, "request for element '" + node.field.name
                    + "' in expression of type " + type_str
                    + ", which does not point to a struct or union"
                )
        if node.field.name not in struct_type.fields:
            raise TypeCheckError(
                node.coord, " request for field '" + node.field.name
                            + "' in expression of type " + type_str
                            + ", which has no such field\n"
                            + "(has fields: " + ", ".join(struct_type.fields) + ")"
            )
        else:
            node_types[node] = struct_type.fields[node.field.name]

    elif t == c_ast.Assignment:
        if node.op != "=":
            raise TypeCheckError(node.coord, "we don't yet handle +=, etc.")

        var_type = get_type(node.lvalue, context, info)
        expr_type = get_type(node.rvalue, context, info)

        ok, reason = assignment_okay(var_type, expr_type, info)
        if not ok:
            raise TypeCheckError(
                node.coord, "can't assign expression of type "
                          + expand_type_name(expr_type, info) + " to variable of type "
                          + expand_type_name(var_type, info) + ": " + reason
            )

    elif t == c_ast.BinaryOp:
        l_type = get_type(node.left, context, info)
        r_type = get_type(node.right, context, info)

        if is_owned_ptr(l_type):
            node_types[node] = unowned_version(l_type, info)
        elif is_owned_ptr(r_type):
            node_types[node] = unowned_version(r_type, info)
        else:
            # NOTE: Doesn't properly check whether the operation makes sense for given types.
            # Also doesn't handle type promotion, etc., so certain operations (like int + float)
            # will return the wrong result.
            node_types[node] = l_type

    elif t == c_ast.UnaryOp:
        if node.op == "*":
            node_type = get_type(node.expr, context, info)
            if is_ptr(node_type, info):
                node_types[node] = node_type.ptrto
            else:
                raise TypeCheckError(
                    node.coord, "Can't dereference expression of non-pointer type: "
                              + expand_type_name(node_type, info)
                )
        elif node.op == "&":
            node_type = get_type(node.expr, context, info)
            node_types[node] = PointerType(node_type, [])
        elif node.op == "sizeof":
            # NOTE: Should technically be size_t
            node_types[node] = NamedType(["int"], [])
        else:
            # it's -, !, ~, ++, or --, so results in the same type of thing as it
            # was used on.
            inner_type = get_type(node.expr, context, info)
            node_types[node] = inner_type

    elif t == c_ast.If:
        cond_type = get_type(node.cond, context, info)

        # Check types of true/false branches.
        get_type(node.iftrue, context, info)
        if node.iffalse is not None:
            get_type(node.iffalse, context, info)

    elif t == c_ast.While or t == c_ast.DoWhile:
        cond_type = get_type(node.cond, context, info)

        # Check type of loop body.
        get_type(node.stmt, context, info)

    elif t == c_ast.ID:
        # Just a variable -- check if it's in scope or not.
        try:
            node_types[node] = context[node.name]
        except KeyError:
            raise TypeCheckError(node.coord, "no variable named " + node.name)

    elif t == c_ast.Constant:
        # Just a constant value.
        if node.type == "string":
            node_types[node] = PointerType(NamedType(["char"], ["const"]), [])
        else:
            node_types[node] = NamedType([node.type], [])

    elif t == c_ast.Cast:
        if is_owned_ptr(convert_type(node.to_type.type, info)):
            if not is_owned_ptr(get_type(node.expr, context, info)):
                # Forbid casting unowned pointer to owned pointer.
                raise TypeCheckError(node.coord, "Cannot cast pointer from unowned to owned.")

        node_types[node] = convert_type(node.to_type.type, info)

    elif t == c_ast.Return:
        if node.expr is not None and str(info['func_return']) != 'void':
            returned_type = get_type(node.expr, context, info)
            ok, reason = assignment_okay(info['func_return'], returned_type, info)
            if not ok:
                raise TypeCheckError(
                    node.coord, "in function " + info['func_name']
                              + ", declared as returning type "
                              + expand_type_name(info['func_return'], info)
                              + ": can't return expression of type "
                              + expand_type_name(returned_type, info)
                              + ": " + reason
                )
        elif node.expr is not None and str(info['func_return']) == 'void':
            raise TypeCheckError(
                node.coord, "returning value from void function " + info['func_name'])
        elif node.expr is None and str(info['func_return']) != 'void':
            raise TypeCheckError(
                node.coord, "empty return from non-void function " + info['func_name'])
        else:
            # Empty return statement in void function, ok.
            pass

    elif t == c_ast.FuncCall:
        if node.name.name == "free":
            # Skip this, since we can't check it anyway
            # (we don't handle void* right now)
            # and pycparser chokes on <stdlib.h>. So we just
            # special-case free() and malloc().
            for param in node.args.exprs:
                # But we still have to mark each node with its type,
                # or else it'll choke later when it tries to see what
                # types the parameters to free() had.
                get_type(param, context, info)
            node_types[node] = None
            return None

        if node.name.name == "malloc":
            for param in node.args.exprs:
                # But we still have to mark each node with its type,
                # or else it'll choke later when it tries to see what
                # types the parameters to free() had.
                get_type(param, context, info)
            node_types[node] = malloc_return_type
            return malloc_return_type

        func_type = function_types[node.name.name]
        return_type = func_type[0]
        param_names = [a[0] for a in func_type[1]]
        param_types = [a[1] for a in func_type[1]]

        for index, param in enumerate(node.args.exprs):
            # Make sure all the parameters match in type
            param_type = get_type(param, context, info)
            # use initialization_okay because it's okay to pass a non-const
            # to a const parameter
            if not initialization_okay(param_type, param_types[index], info):
                raise TypeCheckError(
                    param.coord, "parameter #" + str(index+1)
                               + " (‘" + param_names[index]
                               + "’) to function " + node.name.name
                               + " expects type " + expand_type_name(param_types[index], info)
                               + ", but was passed an expression of type "
                               + expand_type_name(param_type, info) + " instead."
                )

        # If we made it and all the parameters match,
        # then we get a value of the function's return type.

        node_types[node] = return_type
        return return_type

    elif t == c_ast.EmptyStatement:
        pass

    else:
        raise TypeCheckError(node.coord, "don't know how to handle node: " + str(t))

    if node in node_types:
        node_types[node] = unwrap_type(node_types[node], info)
        return node_types[node]


def node_repr(node):
    """ Returns a representation of the node for use as
        a string key in a dictionary.
        If the node is just a variable, this is just the
        variable name. If the node is the address of a
        variable, etc., it will be something like '&a'.
        If it's a struct field, it will be 'a.b', etc. """
    if type(node) == c_ast.Cast:
        return node_repr(node.expr)
    elif type(node) == c_ast.UnaryOp:
        if node.op == "*":
            return "*" + node_repr(node.expr)
        elif node.op == "&":
            return "&" + node_repr(node.expr)
    elif type(node) == c_ast.StructRef:
        return node_repr(node.name) + node.type + node_repr(node.field)
    elif type(node) == c_ast.ID:
        return node.name
    else:
        raise ValueError(str(node.coord.line) + "Can't construct node_repr for " + str(type(node)))


def is_lvalue(node):
    if type(node) in {c_ast.ID, c_ast.ArrayRef, c_ast.StructRef}:
        return True
    if type(node) == c_ast.UnaryOp:
        if node.op == "*":
            return is_lvalue(node.expr)
        else:
            return False
    return False


def unify_conditions(c1, c2):
    """ Given two preconditions, find the 'union'
        of them. (However, the set of variables in
        it is actually the intersection of the
        variables in both, since we don't care
        about any new variables introduced within
        a block.) """
    new_cond = {}

    for var in c1:
        if var in c2:
            if c1[var] == c2[var]:
                new_cond[var] = c1[var]
            elif ((c1[var] == State.UNINIT and c2[var] == State.ZOMBIE)
                  or c1[var] == State.ZOMBIE and c2[var] == State.UNINIT):
                # If uninitialized or zombie, it doesn't really matter.
                new_cond[var] = State.ZOMBIE
            elif State.UNINIT in {c1[var], c2[var]}:
                # Otherwise, if it's maybe uninitialized or maybe valid,
                # that's really bad.
                new_cond[var] = State.MAYBEINIT
            elif State.MAYBEINIT in {c1[var], c2[var]} and State.ZOMBIE not in {c1[var], c2[var]}:
                # If it's maybe initialized but definitely not a zombie,
                # that's bad
                new_cond[var] = State.MAYBEINIT
            else:
                # Also if we're not sure it's a zombie or not. That's
                # pretty bad too.
                new_cond[var] = State.UNKNOWN

    return new_cond


def check_assignment(lval_name, rvalue, lval_type, rval_type, condition, coord, helptext, returning=False):
    if is_ptr(lval_type):
        # Assignment is never OK when the right-side pointer is not OWNED or UNOWNED.
        # Four slightly different error messages depending on the particular state.
        if is_lvalue(rvalue):
            rval_cond = condition[node_repr(rvalue)]
            if rval_cond not in {State.OWNED, State.UNOWNED}:
                if rval_cond == State.UNINIT:
                    explanation = ", which is not initialized."
                if rval_cond == State.MAYBEINIT:
                    explanation = ", which might not be initialized."
                if rval_cond == State.ZOMBIE:
                    explanation = ", which was already moved or freed."
                if rval_cond == State.UNKNOWN:
                    explanation = ", which might have already been moved or freed."

                # Just propagate the error along, so we don't crash later
                # and can get more errors to print out.
                condition[lval_name] = rval_cond
                if rval_cond != State.UNOWNED:
                    condition[node_repr(rvalue)] = State.ZOMBIE
                if not returning:
                    raise TypeCheckError(coord, helptext + "Can't assign from the value of the owned pointer "
                                               + node_repr(rvalue) + explanation)
                else:
                    raise TypeCheckError(coord, helptext + "Can't return the value of the owned pointer "
                                               + node_repr(rvalue) + explanation)

        if is_owned_ptr(lval_type):
            if is_unowned_ptr(rval_type):
                if is_lvalue(rvalue):
                    condition[lval_name] = State.OWNED
                    if not returning:
                        raise TypeCheckError(coord, helptext + "Can't store unowned pointer value "
                                             + node_repr(rvalue)
                                             + " in owned pointer variable "
                                             + lval_name + ".")
                    else:
                        raise TypeCheckError(coord, helptext + "Can't return unowned pointer value "
                                             + node_repr(rvalue) + " when an owned pointer value was expected.")
                else:
                    # Update condition as though error didn't happen -- in case we have more errors later
                    condition[lval_name] = State.OWNED
                    if not returning:
                        raise TypeCheckError(coord, helptext
                                             + "Can't assign an unowned pointer value to owned pointer " + lval_name + ".")
                    else:
                        raise TypeCheckError(coord, helptext + "Can't return an unowned pointer value when "
                                                             + "an owned pointer value was expected.")

            elif is_owned_ptr(rval_type):
                # If the node being assigned to currently doesn't have a valid value....
                if lval_name in condition and condition[lval_name] in {State.ZOMBIE, State.UNINIT}:
                    if returning:
                        operation = "return"
                    else:
                        operation = "assignment"
                    # and the node being assigned DOES have a valid value... (or it's, like, a function return value)
                    if not is_lvalue(rvalue) or condition[node_repr(rvalue)] == State.OWNED:
                        # Move ownership from rvalue to lvalue.
                        if lval_name in condition:
                            # Only make a note of lvalue's state changing if it's actually declared already.
                            # This prevents us from complaining if we assign to a global.
                            condition[lval_name] = State.OWNED
                        if is_lvalue(rvalue):
                            # If lval_type is '@frees', we don't allow access through the rvalue
                            # pointer. Otherwise, we just make it into an unowned pointer.
                            condition[node_repr(rvalue)] = get_final_state(lval_type)
                    elif condition[node_repr(rvalue)] == State.UNKNOWN or condition[node_repr(rvalue)] == State.ZOMBIE:
                        # The rvalue was already moved somewhere else. (or its status is unknown)
                        if lval_name in condition:
                            condition[lval_name] = State.UNKNOWN
                        raise TypeCheckError(coord, helptext + "Can't move pointer value "
                                           + node_repr(rvalue) + " to owned pointer in " + operation + "; it has"
                                           + (" possibly" if condition[node_repr(rvalue)] == State.UNKNOWN else "")
                                           + " already been moved or freed.")
                    else:
                        if lval_name in condition:
                            condition[lval_name] = State.MAYBEINIT
                        raise TypeCheckError(coord, helptext + "Can't move pointer value "
                                           + node_repr(rvalue) + " to owned pointer in " + operation + "; it has"
                                           + (" possibly" if condition[node_repr(rvalue)] == State.MAYBEINIT else "")
                                           + " not been initialized.")
                elif not returning:
                    # Trying to overwrite a possibly-still-owned owned pointer.
                    if lval_name in condition:
                        condition[lval_name] = State.OWNED
                    raise TypeCheckError(coord, helptext + "Can't overwrite the owned pointer value "
                                           + lval_name + "; it has "
                                           + ("possibly " if lval_name not in condition
                                                  or condition[lval_name] == State.MAYBEINIT else "")
                                           + "already been initialized with an owned value.")


def add_to_condition(name, typ, condition, scopes, final, is_param=False):
    """ Add a node of the given type to the current condition.
        Called when we encounter a declaration, and also for
        function parameters.
        is_param should be true if it's a function parameter --
        this makes the initial condition for owned pointers be
        'owned' instead of 'uninitialized' """
    if type(typ) == StructType:
        for field in typ.field_order:
            if is_owned_ptr(typ.fields[field]) or type(typ.fields[field]) == StructType:
                add_to_condition(name + "." + field, typ.fields[field],
                                 condition, scopes, final, is_param)
    else:
        if is_owned_ptr(typ):
            condition[name] = State.UNINIT if not is_param else State.OWNED
            scopes[-1].append(name)
        else:
            condition[name] = State.UNOWNED
            scopes[-1].append(name)

        final[name] = get_final_state(typ)

        unwrapped_node = typ.ptrto
        stars = "*"
        # For pointers-to-owned-pointers (and pointers-to-pointers-to... etc),
        # we need to also add entries for all owned pointed-to pointers in the chain.
        # Hopefully that makes sense
        while is_ptr(unwrapped_node):
            if is_owned_ptr(unwrapped_node):
                condition[stars + name] = State.OWNED
            stars += "*"
            unwrapped_node = unwrapped_node.ptrto


def check_out_of_scope(var, condition, final, node, helptext):
    """ Check whether a variable can properly go out of scope.
        Called whenever an owned-pointer variable goes out of scope,
        or for all currently-accessible variables when the current
        function returns. """
    if condition[var] not in {State.UNOWNED, State.ZOMBIE, State.UNINIT}:
        if condition[var] == State.MAYBEINIT:
            explanation = "was possibly initialized with an owned pointer value, which could leak here"
        elif condition[var] == State.UNKNOWN:
            explanation = "possibly contains a non-freed owned pointer value, which could leak here"
        elif condition[var] == State.OWNED:
            explanation = "still contains an owned pointer value, which will leak here"
        raise TypeCheckError(node.coord, helptext + "pointer value "
                                + var + " " + explanation + ".")
    elif condition[var] == State.UNOWNED and final[var] == State.ZOMBIE:
        raise TypeCheckError(node.coord, helptext + "pointer value "
                                + var + " is unowned (possibly moved somewhere else)"
                                + " but was supposed to be freed (declared by '@frees' annotation).")


# Flag for whether ownership processing is inside a function or not.
in_global_scope = True
# Return type of the current function
func_return_type = None

def check_owners(node, precondition, scopes, final, helptext=""):
    """ Check node for any illegal pointer usage.
        Takes a 'precondition' parameter, a dict mapping
        strings to pointer states.
        The 'scopes' parameter represents which variables were
        introduced in successive outer scopes.
        The 'final' parameter represents the desired final
        pointer states for each variable.
        Returns a 'postcondition', the set of new pointer
        states after the operation corresponding to the
        node. """
    global in_global_scope, func_return_type

    # Find the C type of the node, determined by get_type above.
    node_type = node_types.get(node, None)

    # The python class of the node.
    t = type(node)

    # The current set of pointer states. Returned at the end of the function.
    condition = precondition

    if t == c_ast.FileAST:
        condition = precondition.copy()

        for decl in node.ext:
            try:
                check_owners(decl, condition, scopes, final, helptext)
            except TypeCheckError as e:
                show_error(e)

    elif t == c_ast.FuncDef:
        in_global_scope = False

        func_return_type = node_type

        precondition = condition.copy()
        final = final.copy()
        if node.decl.type.args: # might have no arguments!
            for param in node.decl.type.args.params:
                paramtype = node_types[param]

                if is_owned_ptr(paramtype):
                    add_to_condition(param.name, paramtype, precondition, scopes, final, is_param=True)

        postcondition = check_owners(node.body, precondition, scopes, final, helptext)

        in_global_scope = True
        func_return_type = None

    elif t == c_ast.Compound:
        condition = condition.copy()
        final = final.copy()

        scopes.append([])

        if node.block_items:
            for stmt in node.block_items:
                try:
                    # Update the condition with each line of the block.
                    condition = check_owners(stmt, condition, scopes, final, helptext)
                except TypeCheckError as e:
                    show_error(e)

        for var in scopes[-1]:
            if var in condition:
                # Check the variables going out of scope to make sure they're OK.
                check_out_of_scope(var, condition, final, node, helptext + "at end of this scope: ")

        scopes.pop()

    elif t == c_ast.Decl:
        if is_ptr(node_type):
            if not in_global_scope:
                add_to_condition(node.name, node_type, condition, scopes, final)
            elif is_owned_ptr(node_type):
                raise TypeCheckError(node.coord, "Can't have a global owned pointer.")

        if type(node_type) == StructType and not in_global_scope:
            add_to_condition(node.name, node_type, condition, scopes, final)

        scopes[-1].append(node.name)

        if node.init is not None:
            # Right side might be a function call, so we have to evaluate its ownership as well.
            check_owners(node.init, condition, scopes, final)

            init_type = node_types[node.init]
            check_assignment(node.name, node.init, node_type, init_type, condition, node.coord, helptext)

    elif t == c_ast.Typedef:
        pass

    elif t == c_ast.ArrayRef:
        pass

    elif t == c_ast.StructRef:
        pass

    elif t == c_ast.Assignment:
        if node.op != "=":
            raise TypeCheckError(node.coord, "We don't yet handle assignment other than =.")

        lval_type = node_types[node.lvalue]

        # Right side might be a function call, so we have to evaluate its ownership as well.
        check_owners(node.rvalue, condition, scopes, final)

        rval_type = node_types[node.rvalue]

        check_assignment(node_repr(node.lvalue), node.rvalue, lval_type, rval_type, condition, node.coord, helptext)

    elif t == c_ast.BinaryOp:
        pass

    elif t == c_ast.UnaryOp:
        if is_owned_ptr(node_types[node]):
            if node.op in { "p++", "++p", "p--", "--p" }:
                raise TypeCheckError(node.coord, "Cannot use unary "
                        + ("increment" if "++" in node.op else "decrement")
                        + " on an owned pointer.")

        pass

    elif t == c_ast.DoWhile:
        # Run the loop once...
        after_loop = check_owners(node.stmt, condition, scopes, helptext + "in first iteration of do/while loop: ")
        after_loop = check_owners(node.cond, after_loop, scopes, helptext + "in first iteration of do/while loop: ")

        # and then possibly run it again -- has to work under both conditions
        loop_again = check_owners(node.stmt, after_loop, scopes, helptext + "when running do/while loop again: ")
        loop_again = check_owners(node.cond, loop_again, scopes, helptext + "when running do/while loop again: ")

        condition = unify_conditions(loop_again, after_loop)

    elif t == c_ast.While:
        # Run the loop once...
        after_loop = check_owners(node.cond, condition, scopes, helptext + "in first iteration of while loop: ")
        after_loop = check_owners(node.stmt, after_loop, scopes, helptext + "in first iteration of while loop: ")

        # and then possibly run it again
        loop_again = check_owners(node.cond, after_loop, scopes, helptext + "when running while loop again: ")
        loop_again = check_owners(node.stmt, loop_again, scopes, helptext + "when running while loop again: ")

        # The final one is the unification of running the loop and not running the loop, since
        # with a while loop we might skip over it entirely
        unified = unify_conditions(condition, after_loop)
        condition = unify_conditions(unified, loop_again)

    elif t == c_ast.If:
        after_cond = check_owners(node.cond, condition, scopes, final, helptext)

        # Check the true branch of the if
        after_then = check_owners(node.iftrue, after_cond, scopes, final, helptext)

        # Check the false branch of the if - or if it doesn't exist,
        # use the starting condition as the "after else" condition
        # (since nothing will change if the if's condition is false)
        if node.iffalse is not None:
            after_else = check_owners(node.iffalse, after_cond, scopes, final, helptext)
        else:
            after_else = condition

        # After if, we use the unification of both branches.
        condition = unify_conditions(after_then, after_else)

    elif t == c_ast.ID:
        pass

    elif t == c_ast.Constant:
        pass

    elif t == c_ast.Cast:
        pass

    elif t == c_ast.Return:
        if node.expr:
            check_assignment("", node.expr, func_return_type, node_types[node.expr],
                                          condition, node.coord, helptext, True)

            if is_ptr(node_types[node.expr]):
                if is_lvalue(node.expr):
                    if final[node_repr(node.expr)] == State.UNOWNED:
                        condition[node_repr(node.expr)] = State.UNOWNED
                    else:
                        raise TypeCheckError(node.coord, helptext
                                             + "returning '@frees' owned pointer is illegal; must be freed before "
                                             + "the end of the function.")

        for var in condition:
            check_out_of_scope(var, condition, final, node, helptext + "at return: ")

    elif t == c_ast.FuncCall:
        if node.name.name == "free":
            # We do support marking function parameters as "gets freed by this function."
            # However, pycparser has trouble parsing C headers, so 'free' and 'malloc' are
            # special-cased here at the moment for this 'proof-of-concept' implementation.
            if is_owned_ptr(node_types[node.args.exprs[0]]):
                ptr_cond = condition[node_repr(node.args.exprs[0])]
                if ptr_cond == State.OWNED:
                    condition[node_repr(node.args.exprs[0])] = State.ZOMBIE
                elif ptr_cond in {State.ZOMBIE, State.UNKNOWN}:
                    condition[node_repr(node.args.exprs[0])] = State.ZOMBIE
                    raise TypeCheckError(node.coord, helptext + "Can't free pointer "
                                            + node_repr(node.args.exprs[0])
                                            + ", which was already "
                                            + ("possibly " if ptr_cond == State.UNKNOWN else "")
                                            + "freed or moved."
                                        )
                elif ptr_cond in {State.UNINIT, State.MAYBEINIT}:
                    condition[node_repr(node.args.exprs[0])] = State.ZOMBIE
                    raise TypeCheckError(node.coord, helptext + "Can't free pointer "
                                            + node_repr(node.args.exprs[0])
                                            + ", which "
                                            + ("might not be " if ptr_cond == State.MAYBEINIT else "is not ")
                                            + "initialized."
                                        )
            else:
                raise TypeCheckError(node.coord, helptext + "Can't free unowned pointer.")
        elif node.name.name == "malloc":
            pass
        else:
            # Regular function call. Check that ownership matches its parameter expectations.
            for index, arg in enumerate(node.args.exprs):
                param_name, expected_param_type = function_types[node.name.name][1][index]

                if is_ptr(node_types[arg]):
                    if is_owned_ptr(node_types[arg]):
                        if is_owned_ptr(expected_param_type):
                            # Owned -> owned. OK only if we're sure our argument is already owned.
                            ptr_cond = condition[node_repr(arg)]
                            if ptr_cond == State.OWNED:
                                # Great! Transfer ownership to the function.
                                # Use get_final_state to determine whether the argument is freed or not.
                                condition[node_repr(arg)] = get_final_state(expected_param_type)
                            elif ptr_cond in {State.ZOMBIE, State.UNKNOWN}:
                                condition[node_repr(arg)] = State.ZOMBIE
                                raise TypeCheckError(arg.coord, helptext + "Can't pass "
                                                        + node_repr(arg) + " as owned parameter '"
                                                        + param_name + "' to function "
                                                        + node.name.name + ", since it "
                                                        + (" might have been " if ptr_cond == State.UNKNOWN else " was ")
                                                        + " already freed.")
                            elif ptr_cond in {State.UNINIT, State.MAYBEINIT}:
                                condition[node_repr(arg)] = State.ZOMBIE
                                raise TypeCheckError(arg.coord, helptext + "Can't pass "
                                                        + node_repr(arg) + " as owned parameter '"
                                                        + param_name + "' to function "
                                                        + node.name.name + ", since it "
                                                        + (" might not be " if ptr_cond == State.UNKNOWN else " isn't ")
                                                        + " initialized yet.")
                        else:
                            # Owned -> unowned. That's fine too -- we just don't transfer ownership.
                            pass
                    else:
                        if is_owned_ptr(expected_param_type):
                            # Unowned -> owned. Not okay.
                            raise TypeCheckError(arg.coord, helptext + "Can't pass unowned pointer "
                                                     + node_repr(arg) + " as parameter '"
                                                     + param_name + "' to function "
                                                     + node.name.name + ", which expects an owned pointer argument.")
                        else:
                            # Unowned -> unowned. Fine.
                            pass

    elif t == c_ast.EmptyStatement:
        pass

    else:
        raise TypeCheckError(node.coord, "don't know how to handle node: " + str(t))

    return condition


if __name__ == "__main__":
    if len(sys.argv) > 1:
        with open(sys.argv[1]) as f:
            filecontent = [line.rstrip('\n') for line in f]

        ast = parse_file(sys.argv[1], use_cpp=True)
    else:
        print("required: name of file to parse")
        sys.exit(1)

    # We construct the dictionary mapping nodes to tags.
    get_type(ast, {}, {'typedefs': {}, 'structs': {}, 'states': {}})

    if not error_in_typecheck_phase:
        # Now, we run through the AST again, checking ownership.
        check_owners(ast, {}, [[]], {})
