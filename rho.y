%token IDENT INT FLOAT STRING
%token LOR LAND EQ NEQ LEQ GEQ LSS GTR 
%token OR AND XOR SHL SHR ADD SUB MUL DIV MOD NOT INV
%token ADDA SUBA MULA DIVA MODA ANDA ORA XORA SHLA SHRA
%token IF ELSE FN RET

%start statement

%%
primary_expression
: IDENT
| INT
| FLOAT
| STRING
| '(' expression ')'
;

expression
: conditional_expression
;

conditional_expression
: logical_or_expression
;

logical_or_expression 
: logical_and_expression
| logical_or_expression LOR logical_and_expression
;

logical_and_expression 
: inclusive_or_expression
| logical_and_expression LAND inclusive_or_expression
;

inclusive_or_expression 
: exclusive_or_expression
| inclusive_or_expression OR exclusive_or_expression
;

exclusive_or_expression 
: and_expression
| exclusive_or_expression XOR and_expression
;

and_expression 
: equalty_expression
| and_expression AND equalty_expression
;

equalty_expression 
: relation_expression
| equalty_expression EQ relation_expression
| equalty_expression NEQ relation_expression
;

relation_expression 
: shift_expression
| relation_expression LSS shift_expression
| relation_expression GTR shift_expression
| relation_expression LEQ shift_expression
| relation_expression GEQ shift_expression
;

shift_expression 
: addictive_expression
| shift_expression SHL addictive_expression
| shift_expression SHR addictive_expression
;

addictive_expression 
: multiplicative_expression
| addictive_expression ADD multiplicative_expression
| addictive_expression SUB multiplicative_expression
;

multiplicative_expression 
: cast_expression
| multiplicative_expression MUL cast_expression
| multiplicative_expression DIV cast_expression
| multiplicative_expression MOD cast_expression
;

cast_expression 
: unary_expression
| '(' IDENT ')' cast_expression
;

unary_expression 
: postfix_expression
| unary_operator cast_expression
;

postfix_expression 
: primary_expression
| postfix_expression '[' expression ']'
| postfix_expression '(' ')'
| postfix_expression '(' expression_list ')'
| postfix_expression '.' IDENT
;

expression_list 
: expression
| expression_list ',' expression
;

variable_list
: IDENT
| variable_list ',' IDENT
;

postfix_list
: postfix_expression
| postfix_list ',' postfix_expression
;

assignment: postfix_list assignment_operator expression_list
;

variable_declaration
: variable_list '=' expression_list

function_declaration
: FN IDENT '(' variable_list ')' block

return_statement
: RET expression_list
;

block 
: '{' '}'
| '{' block '}'
| '{' statement_list '}'
;

statement_list 
: statement
| statement_list statement
;

statement
: block
| expression
| assignment
| selection
| iteration
| declaration
| return_statement
;

declaration
: function_declaration
| variable_declaration
;

selection
: IF expression block
| IF expression block ELSE block
| IF expression block ELSE selection
;

iteration
:
;

assignment_operator 
: '='
| ADDA
| SUBA
| MULA
| DIVA
| MODA
| ANDA
| ORA
| XORA
| SHLA
| SHRA
;

unary_operator 
: ADD
| SUB
| NOT
| INV
;
%%