import sys

sys.path.extend(['pycparser'])

from pycparser import parse_file, c_parser, c_ast

filecontent = None

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
        Includes int, char, etc. and also typedefs
        because we don't differentiate these yet.
        Also the names are a list of strings because
        we have stuff like 'unsigned int'. This basically
        comes straight from pycparser. """
    def __init__(self, names):
        self.names = names

    def __str__(self):
        return " ".join(self.names)


class BaseType:
    """ A base type.
        tp = name for the type
        quals = list of qualifiers (const etc) """
    def __init__(self, tp, quals):
        self.tp = tp
        self.quals = quals

    def __str__(self):
        return str(self.tp) + "".join([" " + x for x in self.quals])


class PointerType:
    """ A pointer to another type.
        ptrto = what it's a pointer to
        quals = list of qualifiers (const, etc) """
    def __init__(self, ptrto, quals):
        self.ptrto = ptrto
        self.quals = quals

    def __str__(self):
        return str(self.ptrto) + "*" + "".join([" " + x for x in self.quals])


def convert_type(node):
    """ Convert a c_ast type node to a Type object. """
    t = type(node)

    if t == c_ast.PtrDecl:
        return PointerType(convert_type(node.type), node.quals)
    elif t == c_ast.ArrayDecl:
        return PointerType(convert_type(node.type), [])
    elif t == c_ast.TypeDecl:
        return BaseType(convert_type(node.type), node.quals)
    elif t == c_ast.IdentifierType:
        return NamedType(node.names)
    else:
        raise TypeCheckError(node.coord, "Don't know how to convert type " + str(t))


def assignment_okay(var, expr):
    """ Check whether something of type `expr` can be assigned
        to something of type `var`. """
    if "const" in var.quals:
        # can't reassign const variables
        return False

    return declaration_okay(var, expr)


def declaration_okay(var, expr):
    """ Same as assignment_okay, except that it's okay to assign
        to things that are const because we're initializing. """
    if type(var) == NamedType and type(expr) == BaseType:
        # This is so that if we have e.g. 'const int x = 5', where
        # 5 is of NamedType 'int' and x is of BaseType 'int const',
        # we can still do the assignment correctly.
        return declaration_okay(BaseType(var, []), expr)
    elif type(var) == BaseType and type(expr) == NamedType:
        return declaration_okay(var, BaseType(expr, []))
    elif type(var) != type(expr):
        return False

    if type(var) == PointerType:
        return declaration_okay(var.ptrto, expr.ptrto)
    if type(var) == BaseType:
        return declaration_okay(var.tp, expr.tp)
    if type(var) == NamedType:
        return var.names == expr.names


def show_error(e):
    print(filecontent[e.line - 1])
    print(" " * (e.column - 1) + "^")
    print(e.location + ":", str(e))


def get_type(node, context, info):
    """ Walks over the pycparser-generated AST.
        Checks that a statement has correct type, and also returns
        types of expressions. """
    t = type(node)

    if t == c_ast.FileAST:
        for decl in node.ext:
            try:
                get_type(decl, context, info)
            except TypeCheckError as e:
                show_error(e)
                continue

    elif t == c_ast.FuncDef:
        info_with_return = info.copy()
        info_with_return['func_return'] = convert_type(node.decl.type.type)
        info_with_return['func_name'] = node.decl.name

        # Use a fresh copy of the context dict, so declarations
        # inside each function don't leak outside it, even if we
        # add things to the context.
        func_context = context.copy()
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
        tp = convert_type(node.type)
        if node.init != None:
            expr_tp = get_type(node.init, context, info)
            if not declaration_okay(tp, expr_tp):
                raise TypeCheckError(
                    node.coord, "can't initialize variable " + node.name
                              + " of type " + str(tp) + " with expression of type "
                              + str(expr_tp)
                )
        # Associate the type with the name in context.
        context[node.name] = tp

    elif t == c_ast.ArrayRef:
        subscript_type = get_type(node.subscript, context, info)
        array_type = get_type(node.name, context, info)

        if type(array_type) != PointerType:
            raise TypeCheckError(
                node.coord, "can't subscript type " + str(array_type)
                          + ", which isn't a pointer or array"
            )

    elif t == c_ast.Assignment:
        if node.op != "=":
            raise TypeCheckError(node.coord, "we don't yet handle +=, etc.")

        var_type = get_type(node.lvalue, context, info)
        expr_type = get_type(node.rvalue, context, info)

        if not assignment_okay(var_type, expr_type):
            raise TypeCheckError(
                node.coord, "can't assign expression of type "
                          + str(expr_type) + " to variable of type "
                          + str(var_type)
            )

    elif t == c_ast.BinaryOp:
        l_type = get_type(node.left, context, info)
        r_type = get_type(node.right, context, info)

        # TODO. Need to check if operation makes sense for given types.
        # (like, we shouldn't use division on pointers)
        # TODO. Also, need to handle type promotion etc.
        # (this says e.g. int + float -> int, but it should be float)
        return l_type

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
            return context[node.name]
        except KeyError:
            raise TypeCheckError(node.coord, "no variable named " + node.name)

    elif t == c_ast.Constant:
        # Just a constant value.
        if node.type == "string":
            return PointerType(NamedType(["char"]), ["const"])
        else:
            return NamedType([node.type])

    elif t == c_ast.Return:
        returned_type = get_type(node.expr, context, info)
        if not assignment_okay(info['func_return'], returned_type):
            raise TypeCheckError(
                node.coord, "in function " + info['func_name']
                          + ", declared as returning type "
                          + str(info['func_return'])
                          + ": can't return expression of type "
                          + str(returned_type)
            )

    elif t == c_ast.EmptyStatement:
        pass

    else:
        raise TypeCheckError(node.coord, "don't know how to handle node: " + str(t))


if __name__ == "__main__":
    if len(sys.argv) > 1:
        with open(sys.argv[1]) as f:
            filecontent = [line.rstrip('\n') for line in f]

        ast = parse_file(sys.argv[1], use_cpp=True)
    else:
        print("required: name of file to parse")
        sys.exit(1)

    get_type(ast, {}, {})
