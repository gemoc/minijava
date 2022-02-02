/**
 */
package org.tetrabox.minijava.model.miniJava.util;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EPackage;

import org.eclipse.emf.ecore.util.Switch;

import org.tetrabox.minijava.model.miniJava.And;
import org.tetrabox.minijava.model.miniJava.ArrayAccess;
import org.tetrabox.minijava.model.miniJava.ArrayLength;
import org.tetrabox.minijava.model.miniJava.ArrayTypeRef;
import org.tetrabox.minijava.model.miniJava.Assignee;
import org.tetrabox.minijava.model.miniJava.Assignment;
import org.tetrabox.minijava.model.miniJava.Block;
import org.tetrabox.minijava.model.miniJava.BoolConstant;
import org.tetrabox.minijava.model.miniJava.BooleanTypeRef;
import org.tetrabox.minijava.model.miniJava.ClassRef;
import org.tetrabox.minijava.model.miniJava.Division;
import org.tetrabox.minijava.model.miniJava.Equality;
import org.tetrabox.minijava.model.miniJava.Expression;
import org.tetrabox.minijava.model.miniJava.Field;
import org.tetrabox.minijava.model.miniJava.FieldAccess;
import org.tetrabox.minijava.model.miniJava.ForStatement;
import org.tetrabox.minijava.model.miniJava.IfStatement;
import org.tetrabox.minijava.model.miniJava.Import;
import org.tetrabox.minijava.model.miniJava.Inequality;
import org.tetrabox.minijava.model.miniJava.Inferior;
import org.tetrabox.minijava.model.miniJava.InferiorOrEqual;
import org.tetrabox.minijava.model.miniJava.IntConstant;
import org.tetrabox.minijava.model.miniJava.IntegerTypeRef;
import org.tetrabox.minijava.model.miniJava.Interface;
import org.tetrabox.minijava.model.miniJava.Member;
import org.tetrabox.minijava.model.miniJava.Method;
import org.tetrabox.minijava.model.miniJava.MethodCall;
import org.tetrabox.minijava.model.miniJava.MiniJavaPackage;
import org.tetrabox.minijava.model.miniJava.Minus;
import org.tetrabox.minijava.model.miniJava.Multiplication;
import org.tetrabox.minijava.model.miniJava.NamedElement;
import org.tetrabox.minijava.model.miniJava.Neg;
import org.tetrabox.minijava.model.miniJava.NewArray;
import org.tetrabox.minijava.model.miniJava.NewObject;
import org.tetrabox.minijava.model.miniJava.Not;
import org.tetrabox.minijava.model.miniJava.Null;
import org.tetrabox.minijava.model.miniJava.Or;
import org.tetrabox.minijava.model.miniJava.Parameter;
import org.tetrabox.minijava.model.miniJava.Plus;
import org.tetrabox.minijava.model.miniJava.PrintStatement;
import org.tetrabox.minijava.model.miniJava.Program;
import org.tetrabox.minijava.model.miniJava.Return;
import org.tetrabox.minijava.model.miniJava.SingleTypeRef;
import org.tetrabox.minijava.model.miniJava.Statement;
import org.tetrabox.minijava.model.miniJava.StringConstant;
import org.tetrabox.minijava.model.miniJava.StringTypeRef;
import org.tetrabox.minijava.model.miniJava.Super;
import org.tetrabox.minijava.model.miniJava.Superior;
import org.tetrabox.minijava.model.miniJava.SuperiorOrEqual;
import org.tetrabox.minijava.model.miniJava.Symbol;
import org.tetrabox.minijava.model.miniJava.SymbolRef;
import org.tetrabox.minijava.model.miniJava.This;
import org.tetrabox.minijava.model.miniJava.TypeDeclaration;
import org.tetrabox.minijava.model.miniJava.TypeRef;
import org.tetrabox.minijava.model.miniJava.TypedDeclaration;
import org.tetrabox.minijava.model.miniJava.VariableDeclaration;
import org.tetrabox.minijava.model.miniJava.VoidTypeRef;
import org.tetrabox.minijava.model.miniJava.WhileStatement;

/**
 * <!-- begin-user-doc -->
 * The <b>Switch</b> for the model's inheritance hierarchy.
 * It supports the call {@link #doSwitch(EObject) doSwitch(object)}
 * to invoke the <code>caseXXX</code> method for each class of the model,
 * starting with the actual class of the object
 * and proceeding up the inheritance hierarchy
 * until a non-null result is returned,
 * which is the result of the switch.
 * <!-- end-user-doc -->
 * @see org.tetrabox.minijava.model.miniJava.MiniJavaPackage
 * @generated
 */
public class MiniJavaSwitch<T> extends Switch<T> {
	/**
	 * The cached model package
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected static MiniJavaPackage modelPackage;

	/**
	 * Creates an instance of the switch.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public MiniJavaSwitch() {
		if (modelPackage == null) {
			modelPackage = MiniJavaPackage.eINSTANCE;
		}
	}

	/**
	 * Checks whether this is a switch for the given package.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param ePackage the package in question.
	 * @return whether this is a switch for the given package.
	 * @generated
	 */
	@Override
	protected boolean isSwitchFor(EPackage ePackage) {
		return ePackage == modelPackage;
	}

	/**
	 * Calls <code>caseXXX</code> for each class of the model until one returns a non null result; it yields that result.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the first non-null result returned by a <code>caseXXX</code> call.
	 * @generated
	 */
	@Override
	protected T doSwitch(int classifierID, EObject theEObject) {
		switch (classifierID) {
			case MiniJavaPackage.PROGRAM: {
				Program program = (Program)theEObject;
				T result = caseProgram(program);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.IMPORT: {
				Import import_ = (Import)theEObject;
				T result = caseImport(import_);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.TYPE_DECLARATION: {
				TypeDeclaration typeDeclaration = (TypeDeclaration)theEObject;
				T result = caseTypeDeclaration(typeDeclaration);
				if (result == null) result = caseNamedElement(typeDeclaration);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.CLASS: {
				org.tetrabox.minijava.model.miniJava.Class class_ = (org.tetrabox.minijava.model.miniJava.Class)theEObject;
				T result = caseClass(class_);
				if (result == null) result = caseTypeDeclaration(class_);
				if (result == null) result = caseNamedElement(class_);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.INTERFACE: {
				Interface interface_ = (Interface)theEObject;
				T result = caseInterface(interface_);
				if (result == null) result = caseTypeDeclaration(interface_);
				if (result == null) result = caseNamedElement(interface_);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.MEMBER: {
				Member member = (Member)theEObject;
				T result = caseMember(member);
				if (result == null) result = caseTypedDeclaration(member);
				if (result == null) result = caseNamedElement(member);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.METHOD: {
				Method method = (Method)theEObject;
				T result = caseMethod(method);
				if (result == null) result = caseMember(method);
				if (result == null) result = caseTypedDeclaration(method);
				if (result == null) result = caseNamedElement(method);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.PARAMETER: {
				Parameter parameter = (Parameter)theEObject;
				T result = caseParameter(parameter);
				if (result == null) result = caseSymbol(parameter);
				if (result == null) result = caseTypedDeclaration(parameter);
				if (result == null) result = caseNamedElement(parameter);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.FIELD: {
				Field field = (Field)theEObject;
				T result = caseField(field);
				if (result == null) result = caseMember(field);
				if (result == null) result = caseTypedDeclaration(field);
				if (result == null) result = caseNamedElement(field);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.BLOCK: {
				Block block = (Block)theEObject;
				T result = caseBlock(block);
				if (result == null) result = caseStatement(block);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.STATEMENT: {
				Statement statement = (Statement)theEObject;
				T result = caseStatement(statement);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.PRINT_STATEMENT: {
				PrintStatement printStatement = (PrintStatement)theEObject;
				T result = casePrintStatement(printStatement);
				if (result == null) result = caseStatement(printStatement);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.RETURN: {
				Return return_ = (Return)theEObject;
				T result = caseReturn(return_);
				if (result == null) result = caseStatement(return_);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.IF_STATEMENT: {
				IfStatement ifStatement = (IfStatement)theEObject;
				T result = caseIfStatement(ifStatement);
				if (result == null) result = caseStatement(ifStatement);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.WHILE_STATEMENT: {
				WhileStatement whileStatement = (WhileStatement)theEObject;
				T result = caseWhileStatement(whileStatement);
				if (result == null) result = caseStatement(whileStatement);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.FOR_STATEMENT: {
				ForStatement forStatement = (ForStatement)theEObject;
				T result = caseForStatement(forStatement);
				if (result == null) result = caseStatement(forStatement);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.TYPE_REF: {
				TypeRef typeRef = (TypeRef)theEObject;
				T result = caseTypeRef(typeRef);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.SINGLE_TYPE_REF: {
				SingleTypeRef singleTypeRef = (SingleTypeRef)theEObject;
				T result = caseSingleTypeRef(singleTypeRef);
				if (result == null) result = caseTypeRef(singleTypeRef);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.CLASS_REF: {
				ClassRef classRef = (ClassRef)theEObject;
				T result = caseClassRef(classRef);
				if (result == null) result = caseSingleTypeRef(classRef);
				if (result == null) result = caseTypeRef(classRef);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.NAMED_ELEMENT: {
				NamedElement namedElement = (NamedElement)theEObject;
				T result = caseNamedElement(namedElement);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.TYPED_DECLARATION: {
				TypedDeclaration typedDeclaration = (TypedDeclaration)theEObject;
				T result = caseTypedDeclaration(typedDeclaration);
				if (result == null) result = caseNamedElement(typedDeclaration);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.SYMBOL: {
				Symbol symbol = (Symbol)theEObject;
				T result = caseSymbol(symbol);
				if (result == null) result = caseTypedDeclaration(symbol);
				if (result == null) result = caseNamedElement(symbol);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.VARIABLE_DECLARATION: {
				VariableDeclaration variableDeclaration = (VariableDeclaration)theEObject;
				T result = caseVariableDeclaration(variableDeclaration);
				if (result == null) result = caseSymbol(variableDeclaration);
				if (result == null) result = caseAssignee(variableDeclaration);
				if (result == null) result = caseTypedDeclaration(variableDeclaration);
				if (result == null) result = caseNamedElement(variableDeclaration);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.ASSIGNMENT: {
				Assignment assignment = (Assignment)theEObject;
				T result = caseAssignment(assignment);
				if (result == null) result = caseStatement(assignment);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.ASSIGNEE: {
				Assignee assignee = (Assignee)theEObject;
				T result = caseAssignee(assignee);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.EXPRESSION: {
				Expression expression = (Expression)theEObject;
				T result = caseExpression(expression);
				if (result == null) result = caseStatement(expression);
				if (result == null) result = caseAssignee(expression);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.ARRAY_TYPE_REF: {
				ArrayTypeRef arrayTypeRef = (ArrayTypeRef)theEObject;
				T result = caseArrayTypeRef(arrayTypeRef);
				if (result == null) result = caseTypeRef(arrayTypeRef);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.INTEGER_TYPE_REF: {
				IntegerTypeRef integerTypeRef = (IntegerTypeRef)theEObject;
				T result = caseIntegerTypeRef(integerTypeRef);
				if (result == null) result = caseSingleTypeRef(integerTypeRef);
				if (result == null) result = caseTypeRef(integerTypeRef);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.BOOLEAN_TYPE_REF: {
				BooleanTypeRef booleanTypeRef = (BooleanTypeRef)theEObject;
				T result = caseBooleanTypeRef(booleanTypeRef);
				if (result == null) result = caseSingleTypeRef(booleanTypeRef);
				if (result == null) result = caseTypeRef(booleanTypeRef);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.STRING_TYPE_REF: {
				StringTypeRef stringTypeRef = (StringTypeRef)theEObject;
				T result = caseStringTypeRef(stringTypeRef);
				if (result == null) result = caseSingleTypeRef(stringTypeRef);
				if (result == null) result = caseTypeRef(stringTypeRef);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.VOID_TYPE_REF: {
				VoidTypeRef voidTypeRef = (VoidTypeRef)theEObject;
				T result = caseVoidTypeRef(voidTypeRef);
				if (result == null) result = caseSingleTypeRef(voidTypeRef);
				if (result == null) result = caseTypeRef(voidTypeRef);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.OR: {
				Or or = (Or)theEObject;
				T result = caseOr(or);
				if (result == null) result = caseExpression(or);
				if (result == null) result = caseStatement(or);
				if (result == null) result = caseAssignee(or);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.AND: {
				And and = (And)theEObject;
				T result = caseAnd(and);
				if (result == null) result = caseExpression(and);
				if (result == null) result = caseStatement(and);
				if (result == null) result = caseAssignee(and);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.EQUALITY: {
				Equality equality = (Equality)theEObject;
				T result = caseEquality(equality);
				if (result == null) result = caseExpression(equality);
				if (result == null) result = caseStatement(equality);
				if (result == null) result = caseAssignee(equality);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.INEQUALITY: {
				Inequality inequality = (Inequality)theEObject;
				T result = caseInequality(inequality);
				if (result == null) result = caseExpression(inequality);
				if (result == null) result = caseStatement(inequality);
				if (result == null) result = caseAssignee(inequality);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.SUPERIOR_OR_EQUAL: {
				SuperiorOrEqual superiorOrEqual = (SuperiorOrEqual)theEObject;
				T result = caseSuperiorOrEqual(superiorOrEqual);
				if (result == null) result = caseExpression(superiorOrEqual);
				if (result == null) result = caseStatement(superiorOrEqual);
				if (result == null) result = caseAssignee(superiorOrEqual);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.INFERIOR_OR_EQUAL: {
				InferiorOrEqual inferiorOrEqual = (InferiorOrEqual)theEObject;
				T result = caseInferiorOrEqual(inferiorOrEqual);
				if (result == null) result = caseExpression(inferiorOrEqual);
				if (result == null) result = caseStatement(inferiorOrEqual);
				if (result == null) result = caseAssignee(inferiorOrEqual);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.SUPERIOR: {
				Superior superior = (Superior)theEObject;
				T result = caseSuperior(superior);
				if (result == null) result = caseExpression(superior);
				if (result == null) result = caseStatement(superior);
				if (result == null) result = caseAssignee(superior);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.INFERIOR: {
				Inferior inferior = (Inferior)theEObject;
				T result = caseInferior(inferior);
				if (result == null) result = caseExpression(inferior);
				if (result == null) result = caseStatement(inferior);
				if (result == null) result = caseAssignee(inferior);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.PLUS: {
				Plus plus = (Plus)theEObject;
				T result = casePlus(plus);
				if (result == null) result = caseExpression(plus);
				if (result == null) result = caseStatement(plus);
				if (result == null) result = caseAssignee(plus);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.MINUS: {
				Minus minus = (Minus)theEObject;
				T result = caseMinus(minus);
				if (result == null) result = caseExpression(minus);
				if (result == null) result = caseStatement(minus);
				if (result == null) result = caseAssignee(minus);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.MULTIPLICATION: {
				Multiplication multiplication = (Multiplication)theEObject;
				T result = caseMultiplication(multiplication);
				if (result == null) result = caseExpression(multiplication);
				if (result == null) result = caseStatement(multiplication);
				if (result == null) result = caseAssignee(multiplication);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.DIVISION: {
				Division division = (Division)theEObject;
				T result = caseDivision(division);
				if (result == null) result = caseExpression(division);
				if (result == null) result = caseStatement(division);
				if (result == null) result = caseAssignee(division);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.ARRAY_ACCESS: {
				ArrayAccess arrayAccess = (ArrayAccess)theEObject;
				T result = caseArrayAccess(arrayAccess);
				if (result == null) result = caseExpression(arrayAccess);
				if (result == null) result = caseStatement(arrayAccess);
				if (result == null) result = caseAssignee(arrayAccess);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.ARRAY_LENGTH: {
				ArrayLength arrayLength = (ArrayLength)theEObject;
				T result = caseArrayLength(arrayLength);
				if (result == null) result = caseExpression(arrayLength);
				if (result == null) result = caseStatement(arrayLength);
				if (result == null) result = caseAssignee(arrayLength);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.NOT: {
				Not not = (Not)theEObject;
				T result = caseNot(not);
				if (result == null) result = caseExpression(not);
				if (result == null) result = caseStatement(not);
				if (result == null) result = caseAssignee(not);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.NEG: {
				Neg neg = (Neg)theEObject;
				T result = caseNeg(neg);
				if (result == null) result = caseExpression(neg);
				if (result == null) result = caseStatement(neg);
				if (result == null) result = caseAssignee(neg);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.FIELD_ACCESS: {
				FieldAccess fieldAccess = (FieldAccess)theEObject;
				T result = caseFieldAccess(fieldAccess);
				if (result == null) result = caseExpression(fieldAccess);
				if (result == null) result = caseStatement(fieldAccess);
				if (result == null) result = caseAssignee(fieldAccess);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.METHOD_CALL: {
				MethodCall methodCall = (MethodCall)theEObject;
				T result = caseMethodCall(methodCall);
				if (result == null) result = caseExpression(methodCall);
				if (result == null) result = caseStatement(methodCall);
				if (result == null) result = caseAssignee(methodCall);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.STRING_CONSTANT: {
				StringConstant stringConstant = (StringConstant)theEObject;
				T result = caseStringConstant(stringConstant);
				if (result == null) result = caseExpression(stringConstant);
				if (result == null) result = caseStatement(stringConstant);
				if (result == null) result = caseAssignee(stringConstant);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.INT_CONSTANT: {
				IntConstant intConstant = (IntConstant)theEObject;
				T result = caseIntConstant(intConstant);
				if (result == null) result = caseExpression(intConstant);
				if (result == null) result = caseStatement(intConstant);
				if (result == null) result = caseAssignee(intConstant);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.BOOL_CONSTANT: {
				BoolConstant boolConstant = (BoolConstant)theEObject;
				T result = caseBoolConstant(boolConstant);
				if (result == null) result = caseExpression(boolConstant);
				if (result == null) result = caseStatement(boolConstant);
				if (result == null) result = caseAssignee(boolConstant);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.THIS: {
				This this_ = (This)theEObject;
				T result = caseThis(this_);
				if (result == null) result = caseExpression(this_);
				if (result == null) result = caseStatement(this_);
				if (result == null) result = caseAssignee(this_);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.SUPER: {
				Super super_ = (Super)theEObject;
				T result = caseSuper(super_);
				if (result == null) result = caseExpression(super_);
				if (result == null) result = caseStatement(super_);
				if (result == null) result = caseAssignee(super_);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.NULL: {
				Null null_ = (Null)theEObject;
				T result = caseNull(null_);
				if (result == null) result = caseExpression(null_);
				if (result == null) result = caseStatement(null_);
				if (result == null) result = caseAssignee(null_);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.NEW_OBJECT: {
				NewObject newObject = (NewObject)theEObject;
				T result = caseNewObject(newObject);
				if (result == null) result = caseExpression(newObject);
				if (result == null) result = caseStatement(newObject);
				if (result == null) result = caseAssignee(newObject);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.NEW_ARRAY: {
				NewArray newArray = (NewArray)theEObject;
				T result = caseNewArray(newArray);
				if (result == null) result = caseExpression(newArray);
				if (result == null) result = caseStatement(newArray);
				if (result == null) result = caseAssignee(newArray);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			case MiniJavaPackage.SYMBOL_REF: {
				SymbolRef symbolRef = (SymbolRef)theEObject;
				T result = caseSymbolRef(symbolRef);
				if (result == null) result = caseExpression(symbolRef);
				if (result == null) result = caseStatement(symbolRef);
				if (result == null) result = caseAssignee(symbolRef);
				if (result == null) result = defaultCase(theEObject);
				return result;
			}
			default: return defaultCase(theEObject);
		}
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Program</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Program</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseProgram(Program object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Import</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Import</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseImport(Import object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Type Declaration</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Type Declaration</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseTypeDeclaration(TypeDeclaration object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Class</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Class</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseClass(org.tetrabox.minijava.model.miniJava.Class object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Interface</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Interface</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseInterface(Interface object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Member</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Member</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseMember(Member object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Method</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Method</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseMethod(Method object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Parameter</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Parameter</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseParameter(Parameter object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Field</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Field</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseField(Field object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Block</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Block</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseBlock(Block object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Statement</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Statement</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseStatement(Statement object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Print Statement</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Print Statement</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T casePrintStatement(PrintStatement object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Return</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Return</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseReturn(Return object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>If Statement</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>If Statement</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseIfStatement(IfStatement object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>While Statement</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>While Statement</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseWhileStatement(WhileStatement object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>For Statement</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>For Statement</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseForStatement(ForStatement object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Type Ref</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Type Ref</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseTypeRef(TypeRef object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Single Type Ref</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Single Type Ref</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseSingleTypeRef(SingleTypeRef object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Class Ref</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Class Ref</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseClassRef(ClassRef object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Named Element</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Named Element</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseNamedElement(NamedElement object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Typed Declaration</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Typed Declaration</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseTypedDeclaration(TypedDeclaration object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Symbol</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Symbol</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseSymbol(Symbol object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Variable Declaration</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Variable Declaration</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseVariableDeclaration(VariableDeclaration object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Assignment</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Assignment</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseAssignment(Assignment object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Assignee</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Assignee</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseAssignee(Assignee object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Expression</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Expression</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseExpression(Expression object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Array Type Ref</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Array Type Ref</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseArrayTypeRef(ArrayTypeRef object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Integer Type Ref</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Integer Type Ref</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseIntegerTypeRef(IntegerTypeRef object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Boolean Type Ref</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Boolean Type Ref</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseBooleanTypeRef(BooleanTypeRef object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>String Type Ref</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>String Type Ref</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseStringTypeRef(StringTypeRef object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Void Type Ref</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Void Type Ref</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseVoidTypeRef(VoidTypeRef object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Or</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Or</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseOr(Or object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>And</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>And</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseAnd(And object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Equality</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Equality</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseEquality(Equality object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Inequality</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Inequality</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseInequality(Inequality object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Superior Or Equal</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Superior Or Equal</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseSuperiorOrEqual(SuperiorOrEqual object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Inferior Or Equal</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Inferior Or Equal</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseInferiorOrEqual(InferiorOrEqual object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Superior</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Superior</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseSuperior(Superior object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Inferior</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Inferior</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseInferior(Inferior object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Plus</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Plus</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T casePlus(Plus object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Minus</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Minus</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseMinus(Minus object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Multiplication</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Multiplication</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseMultiplication(Multiplication object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Division</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Division</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseDivision(Division object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Array Access</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Array Access</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseArrayAccess(ArrayAccess object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Array Length</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Array Length</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseArrayLength(ArrayLength object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Not</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Not</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseNot(Not object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Neg</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Neg</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseNeg(Neg object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Field Access</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Field Access</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseFieldAccess(FieldAccess object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Method Call</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Method Call</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseMethodCall(MethodCall object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>String Constant</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>String Constant</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseStringConstant(StringConstant object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Int Constant</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Int Constant</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseIntConstant(IntConstant object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Bool Constant</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Bool Constant</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseBoolConstant(BoolConstant object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>This</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>This</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseThis(This object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Super</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Super</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseSuper(Super object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Null</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Null</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseNull(Null object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>New Object</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>New Object</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseNewObject(NewObject object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>New Array</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>New Array</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseNewArray(NewArray object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>Symbol Ref</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>Symbol Ref</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
	 * @generated
	 */
	public T caseSymbolRef(SymbolRef object) {
		return null;
	}

	/**
	 * Returns the result of interpreting the object as an instance of '<em>EObject</em>'.
	 * <!-- begin-user-doc -->
	 * This implementation returns null;
	 * returning a non-null result will terminate the switch, but this is the last case anyway.
	 * <!-- end-user-doc -->
	 * @param object the target of the switch.
	 * @return the result of interpreting the object as an instance of '<em>EObject</em>'.
	 * @see #doSwitch(org.eclipse.emf.ecore.EObject)
	 * @generated
	 */
	@Override
	public T defaultCase(EObject object) {
		return null;
	}

} //MiniJavaSwitch
