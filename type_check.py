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
                             "int", "float", "double", "char" }:
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
        if len(name) != 0:
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
        (They might be at different nested typedefs, for example.) """
    if info is None:
        return type(t) == PointerType and '@owned' in t.quals
    return is_ptr(t, info) and '@owned' in unwrap_type(t, info).quals


def is_unowned_ptr(t, info=None):
    return is_ptr(t, info) and not is_owned_ptr(t, info)


def convert_type(node, info):
    def recurse(node, info, quals):
        """ Convert a c_ast type node to a Type object. """
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
                # NOTE: I think this will fail if we have like 'struct X;'
                # alone on its own line. But unsure if this matters that much.
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
        # it's actually wrong.
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
        if type(t) == NamedType and t.is_typedef:
            return recurse(info['typedefs'][t.names[0]], info, extra_quals + t.quals)
        else:
            fresh_type = copy.deepcopy(t)
            fresh_type.quals += extra_quals
            return fresh_type
    return recurse(t, info, [])


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

def get_type(node, context, info):
    """ Walks over the pycparser-generated AST.
        Checks that a statement has correct type, and also returns
        types of expressions. """
    t = type(node)

    if t == c_ast.FileAST:
        #print(node)
        for decl in node.ext:
            try:
                get_type(decl, context, info)
            except TypeCheckError as e:
                show_error(e)
                continue

    elif t == c_ast.FuncDef:
        info_with_return = copy.deepcopy(info)
        info_with_return['func_return'] = convert_type(node.decl.type.type, info)
        info_with_return['func_name'] = node.decl.name

        # Use a fresh copy of the context dict, so declarations
        # inside each function don't leak outside it, even if we
        # add things to the context.
        func_context = context.copy()

        if node.decl.type.args is not None:
            for param in node.decl.type.args.params:
                # Put parameters into function scope.
                get_type(param, func_context, info_with_return)

        get_type(node.body, func_context, info_with_return)

    elif t == c_ast.Compound:
        # As above.
        block_context = context.copy()
        for stmt in node.block_items:
            try:
                get_type(stmt, block_context, info)
            except TypeCheckError as e:
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

        # TODO. Need to check if operation makes sense for given types.
        # (like, we shouldn't use division on pointers)
        # TODO. Also, need to handle type promotion etc.
        # (this says e.g. int + float -> int, but it should be float)
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
        node_types[node] = convert_type(node.to_type.type, info)

    elif t == c_ast.Return:
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

    elif t == c_ast.FuncCall:
        # TODO Handle function calls.
        for param in node.args.exprs:
            # We'll deal with this later...
            get_type(param, context, info)

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
            elif c1[var] == State.UNINIT or c2[var] == State.UNINIT:
                # Otherwise, if it's maybe uninitialized or maybe valid,
                # that's really bad.
                new_cond[var] = State.MAYBEINIT
            else:
                # Also if we're not sure it's a zombie or not. That's
                # pretty bad too.
                new_cond[var] = State.UNKNOWN

    return new_cond


def check_assignment(lval_name, rvalue, lval_type, rval_type, condition, coord, helptext):
    if is_ptr(lval_type):
        # Assignment is never OK when the right-side pointer is not OWNED or UNOWNED.
        # Four slightly different error messages depending on the particular state.
        if is_lvalue(rvalue):
            rval_cond = condition[node_repr(rvalue)]
            if rval_cond not in {State.OWNED, State.UNOWNED}:
                if rval_cond == State.UNINIT:
                    explanation = ", which is not yet initialized."
                if rval_cond == State.MAYBEINIT:
                    explanation = ", which might not yet be initialized."
                if rval_cond == State.ZOMBIE:
                    explanation = ", which was already moved or freed."
                if rval_cond == State.UNKNOWN:
                    explanation = ", which might have already been moved or freed."

                # Just propagate the error along, so we don't crash later
                # and can get more errors to print out.
                condition[lval_name] = rval_cond
                raise TypeCheckError(coord, helptext + "Can't assign from the value of the owned pointer "
                                           + node_repr(rvalue) + explanation)
        if is_owned_ptr(lval_type):
            if is_unowned_ptr(rval_type):
                if is_lvalue(rvalue):
                    condition[lval_name] = State.OWNED
                    raise TypeCheckError(coord, helptext + "Can't store unowned pointer value "
                                         + node_repr(rvalue)
                                         + " in owned pointer variable "
                                         + lval_name + ".")
                else:
                    raise TypeCheckError(coord, helptext
                                         + "Can't assign an unowned pointer value to owned pointer variable " + lval_name + ".")
            elif is_owned_ptr(rval_type):
                # If the node being assigned to currently doesn't have a valid value....
                if condition[lval_name] in {State.ZOMBIE, State.UNINIT}:
                    # and the node being assigned DOES have a valid value... (or it's, like, a function return value)
                    if not is_lvalue(rvalue) or condition[node_repr(rvalue)] == State.OWNED:
                        # Move ownership from rvalue to lvalue.
                        condition[lval_name] = State.OWNED
                        if is_lvalue(rvalue):
                            condition[node_repr(rvalue)] = State.ZOMBIE
                    elif condition[node_repr(rvalue)] == State.UNKNOWN or condition[node_repr(rvalue)] == State.ZOMBIE:
                        # The rvalue was already moved somewhere else. (or its status is unknown)
                        condition[lval_name] = State.UNKNOWN
                        raise TypeCheckError(coord, helptext + "Can't move pointer value "
                                           + node_repr(rvalue) + " to owned pointer in assignment; it has"
                                           + (" possibly" if condition[node_repr(rvalue)] == State.UNKNOWN else "")
                                           + " already been moved.")
                    else:
                        condition[lval_name] = State.MAYBEINIT
                        raise TypeCheckError(coord, helptext + "Can't move pointer value "
                                           + node_repr(rvalue) + " to owned pointer in assignment; it has"
                                           + (" possibly" if condition[node_repr(rvalue)] == State.MAYBEINIT else "")
                                           + " not yet been initialized.")
                else:
                    # Trying to overwrite a possibly-still-owned owned pointer.
                    raise TypeCheckError(coord, helptext + "Can't overwrite the owned pointer value "
                                           + lval_name + "; it has "
                                           + ("possibly " if condition[lval_name] == State.MAYBEINIT else "")
                                           + "already been initialized with an owned value.")


def check_owners(node, precondition, helptext=""):
    """ Check node for any illegal pointer usage.
        Takes a 'precondition' parameter, a dict mapping
        strings to pointer states.
        Returns a 'postcondition', the set of new pointer
        states after the operation corresponding to the
        node. """
    # Find the C type of the node, determined by get_type above.
    node_type = node_types.get(node, None)

    # The python class of the node.
    t = type(node)

    # The current set of pointer states. Returned at the end of the function.
    condition = precondition.copy()

    if t == c_ast.FileAST:
        for decl in node.ext:
            try:
                check_owners(decl, precondition, helptext)
            except TypeCheckError as e:
                show_error(e)

    elif t == c_ast.FuncDef:
        postcondition = check_owners(node.body, precondition, helptext)

    elif t == c_ast.Compound:
        condition = precondition

        for stmt in node.block_items:
            try:
                # Update the condition with each line of the block.
                #print(filecontent[stmt.coord.line-1])
                #print(" (1)", condition)
                condition = check_owners(stmt, condition, helptext)
                #print(" (2)", condition)
            except TypeCheckError as e:
                show_error(e)
                break

    elif t == c_ast.Decl:
        if is_ptr(node_type):
            if is_owned_ptr(node_type):
                condition[node.name] = State.UNINIT
            else:
                condition[node.name] = State.UNOWNED

        if node.init is not None:
            init_type = node_types[node.init]
            check_assignment(node.name, node.init, node_type, init_type, condition, node.coord, helptext)

    elif t == c_ast.Typedef:
        pass

    elif t == c_ast.ArrayRef:
        # TODO
        pass

    elif t == c_ast.StructRef:
        # TODO
        pass

    elif t == c_ast.Assignment:
        if node.op != "=":
            raise TypeCheckError(node.coord, "We don't yet handle assignment other than =.")

        lval_type = node_types[node.lvalue]
        rval_type = node_types[node.rvalue]

        check_assignment(node_repr(node.lvalue), node.rvalue, lval_type, rval_type, condition, node.coord, helptext)

    elif t == c_ast.BinaryOp:
        pass

    elif t == c_ast.UnaryOp:
        # TODO Forbid 'p++' etc. on owned pointers
        pass

    elif t == c_ast.DoWhile:
        # Run the loop once...
        after_loop = check_owners(node.stmt, condition, helptext + "in first iteration of do/while loop: ")
        after_loop = check_owners(node.cond, after_loop, helptext + "in first iteration of do/while loop: ")

        # and then possibly run it again -- has to work under both conditions
        loop_again = check_owners(node.stmt, after_loop, helptext + "when running do/while loop again: ")
        loop_again = check_owners(node.cond, loop_again, helptext + "when running do/while loop again: ")

        condition = unify_conditions(loop_again, after_loop)

    elif t == c_ast.While:
        # Run the loop once...
        after_loop = check_owners(node.cond, condition, helptext + "in first iteration of while loop: ")
        after_loop = check_owners(node.stmt, after_loop, helptext + "in first iteration of while loop: ")

        # and then possibly run it again
        loop_again = check_owners(node.cond, after_loop, helptext + "when running while loop again: ")
        loop_again = check_owners(node.stmt, loop_again, helptext + "when running while loop again: ")

        # The final one is the unification of running the loop and not running the loop, since
        # with a while loop we might skip over it entirely
        unified = unify_conditions(condition, after_loop)
        condition = unify_conditions(unified, loop_again)

    elif t == c_ast.If:
        after_cond = check_owners(node.cond, condition, helptext)

        # Check the true branch of the if
        after_then = check_owners(node.iftrue, after_cond, helptext)

        # Check the false branch of the if - or if it doesn't exist,
        # use the starting condition as the "after else" thing
        if node.iffalse is not None:
            after_else = check_owners(node.iffalse, after_cond, helptext)
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
        if is_ptr(node_types[node.expr]):
            if is_lvalue(node.expr):
                # TODO Check ownership matches function return expectation.
                condition[node_repr(node.expr)] = State.ZOMBIE

        for var in condition:
            if condition[var] not in {State.UNOWNED, State.ZOMBIE, State.UNINIT}:
                if condition[var] == State.MAYBEINIT:
                    explanation = "possibly contains an owned pointer value, which could leak"
                elif condition[var] == State.UNKNOWN:
                    explanation = "possibly contains an owned pointer value, which could leak"
                elif condition[var] == State.OWNED:
                    explanation = "still contains an owned pointer value, which will leak"
                raise TypeCheckError(node.coord, helptext + "at return, pointer value "
                                        + var + " " + explanation + ".")

    elif t == c_ast.FuncCall:
        # TODO Handle arbitrary func. calls
        if node.name.name == "free":
            if is_owned_ptr(node_types[node.args.exprs[0]]):
                ptr_cond = condition[node_repr(node.args.exprs[0])]
                if ptr_cond == State.OWNED:
                    condition[node_repr(node.args.exprs[0])] = State.ZOMBIE
                elif ptr_cond in {State.ZOMBIE, State.UNKNOWN}:
                    raise TypeCheckError(node.coord, helptext + "Can't free pointer "
                                            + node_repr(node.args.exprs[0])
                                            + ", which was already "
                                            + ("possibly " if condition[node_repr(node.args.exprs[0])] == State.UNKNOWN else "")
                                            + "freed or moved."
                                        )
                elif ptr_cond in {State.UNINIT, State.MAYBEINIT}:
                    raise TypeCheckError(node.coord, helptext + "Can't free pointer "
                                            + node_repr(node.args.exprs[0])
                                            + ", which "
                                            + ("might not be " if condition[node_repr(node.args.exprs[0])] == State.MAYBEINIT else "is not yet ")
                                            + "initialized."
                                        )
            else:
                raise TypeCheckError(node.coord, helptext + "Can't free unowned pointer.")

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

    #print(ast)
    # We construct the dictionary mapping nodes to tags.
    get_type(ast, {}, {'typedefs': {}, 'structs': {}, 'states': {}})

    # Now, we run through the AST again, checking ownership.
    check_owners(ast, {})
