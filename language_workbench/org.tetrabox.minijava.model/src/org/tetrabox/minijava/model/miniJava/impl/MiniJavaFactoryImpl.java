/**
 */
package org.tetrabox.minijava.model.miniJava.impl;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EDataType;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EPackage;

import org.eclipse.emf.ecore.impl.EFactoryImpl;

import org.eclipse.emf.ecore.plugin.EcorePlugin;

import org.tetrabox.minijava.model.miniJava.AccessLevel;
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
import org.tetrabox.minijava.model.miniJava.MiniJavaFactory;
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
 * An implementation of the model <b>Factory</b>.
 * <!-- end-user-doc -->
 * @generated
 */
public class MiniJavaFactoryImpl extends EFactoryImpl implements MiniJavaFactory {
	/**
	 * Creates the default factory implementation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static MiniJavaFactory init() {
		try {
			MiniJavaFactory theMiniJavaFactory = (MiniJavaFactory)EPackage.Registry.INSTANCE.getEFactory(MiniJavaPackage.eNS_URI);
			if (theMiniJavaFactory != null) {
				return theMiniJavaFactory;
			}
		}
		catch (Exception exception) {
			EcorePlugin.INSTANCE.log(exception);
		}
		return new MiniJavaFactoryImpl();
	}

	/**
	 * Creates an instance of the factory.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public MiniJavaFactoryImpl() {
		super();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public EObject create(EClass eClass) {
		switch (eClass.getClassifierID()) {
			case MiniJavaPackage.PROGRAM: return createProgram();
			case MiniJavaPackage.IMPORT: return createImport();
			case MiniJavaPackage.TYPE_DECLARATION: return createTypeDeclaration();
			case MiniJavaPackage.CLASS: return createClass();
			case MiniJavaPackage.INTERFACE: return createInterface();
			case MiniJavaPackage.MEMBER: return createMember();
			case MiniJavaPackage.METHOD: return createMethod();
			case MiniJavaPackage.PARAMETER: return createParameter();
			case MiniJavaPackage.FIELD: return createField();
			case MiniJavaPackage.BLOCK: return createBlock();
			case MiniJavaPackage.STATEMENT: return createStatement();
			case MiniJavaPackage.PRINT_STATEMENT: return createPrintStatement();
			case MiniJavaPackage.RETURN: return createReturn();
			case MiniJavaPackage.IF_STATEMENT: return createIfStatement();
			case MiniJavaPackage.WHILE_STATEMENT: return createWhileStatement();
			case MiniJavaPackage.FOR_STATEMENT: return createForStatement();
			case MiniJavaPackage.TYPE_REF: return createTypeRef();
			case MiniJavaPackage.SINGLE_TYPE_REF: return createSingleTypeRef();
			case MiniJavaPackage.CLASS_REF: return createClassRef();
			case MiniJavaPackage.NAMED_ELEMENT: return createNamedElement();
			case MiniJavaPackage.TYPED_DECLARATION: return createTypedDeclaration();
			case MiniJavaPackage.SYMBOL: return createSymbol();
			case MiniJavaPackage.VARIABLE_DECLARATION: return createVariableDeclaration();
			case MiniJavaPackage.ASSIGNMENT: return createAssignment();
			case MiniJavaPackage.ASSIGNEE: return createAssignee();
			case MiniJavaPackage.EXPRESSION: return createExpression();
			case MiniJavaPackage.ARRAY_TYPE_REF: return createArrayTypeRef();
			case MiniJavaPackage.INTEGER_TYPE_REF: return createIntegerTypeRef();
			case MiniJavaPackage.BOOLEAN_TYPE_REF: return createBooleanTypeRef();
			case MiniJavaPackage.STRING_TYPE_REF: return createStringTypeRef();
			case MiniJavaPackage.VOID_TYPE_REF: return createVoidTypeRef();
			case MiniJavaPackage.OR: return createOr();
			case MiniJavaPackage.AND: return createAnd();
			case MiniJavaPackage.EQUALITY: return createEquality();
			case MiniJavaPackage.INEQUALITY: return createInequality();
			case MiniJavaPackage.SUPERIOR_OR_EQUAL: return createSuperiorOrEqual();
			case MiniJavaPackage.INFERIOR_OR_EQUAL: return createInferiorOrEqual();
			case MiniJavaPackage.SUPERIOR: return createSuperior();
			case MiniJavaPackage.INFERIOR: return createInferior();
			case MiniJavaPackage.PLUS: return createPlus();
			case MiniJavaPackage.MINUS: return createMinus();
			case MiniJavaPackage.MULTIPLICATION: return createMultiplication();
			case MiniJavaPackage.DIVISION: return createDivision();
			case MiniJavaPackage.ARRAY_ACCESS: return createArrayAccess();
			case MiniJavaPackage.ARRAY_LENGTH: return createArrayLength();
			case MiniJavaPackage.NOT: return createNot();
			case MiniJavaPackage.NEG: return createNeg();
			case MiniJavaPackage.FIELD_ACCESS: return createFieldAccess();
			case MiniJavaPackage.METHOD_CALL: return createMethodCall();
			case MiniJavaPackage.STRING_CONSTANT: return createStringConstant();
			case MiniJavaPackage.INT_CONSTANT: return createIntConstant();
			case MiniJavaPackage.BOOL_CONSTANT: return createBoolConstant();
			case MiniJavaPackage.THIS: return createThis();
			case MiniJavaPackage.SUPER: return createSuper();
			case MiniJavaPackage.NULL: return createNull();
			case MiniJavaPackage.NEW_OBJECT: return createNewObject();
			case MiniJavaPackage.NEW_ARRAY: return createNewArray();
			case MiniJavaPackage.SYMBOL_REF: return createSymbolRef();
			default:
				throw new IllegalArgumentException("The class '" + eClass.getName() + "' is not a valid classifier");
		}
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Object createFromString(EDataType eDataType, String initialValue) {
		switch (eDataType.getClassifierID()) {
			case MiniJavaPackage.ACCESS_LEVEL:
				return createAccessLevelFromString(eDataType, initialValue);
			default:
				throw new IllegalArgumentException("The datatype '" + eDataType.getName() + "' is not a valid classifier");
		}
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public String convertToString(EDataType eDataType, Object instanceValue) {
		switch (eDataType.getClassifierID()) {
			case MiniJavaPackage.ACCESS_LEVEL:
				return convertAccessLevelToString(eDataType, instanceValue);
			default:
				throw new IllegalArgumentException("The datatype '" + eDataType.getName() + "' is not a valid classifier");
		}
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Program createProgram() {
		ProgramImpl program = new ProgramImpl();
		return program;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Import createImport() {
		ImportImpl import_ = new ImportImpl();
		return import_;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public TypeDeclaration createTypeDeclaration() {
		TypeDeclarationImpl typeDeclaration = new TypeDeclarationImpl();
		return typeDeclaration;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public org.tetrabox.minijava.model.miniJava.Class createClass() {
		ClassImpl class_ = new ClassImpl();
		return class_;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Interface createInterface() {
		InterfaceImpl interface_ = new InterfaceImpl();
		return interface_;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Member createMember() {
		MemberImpl member = new MemberImpl();
		return member;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Method createMethod() {
		MethodImpl method = new MethodImpl();
		return method;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Parameter createParameter() {
		ParameterImpl parameter = new ParameterImpl();
		return parameter;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Field createField() {
		FieldImpl field = new FieldImpl();
		return field;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Block createBlock() {
		BlockImpl block = new BlockImpl();
		return block;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Statement createStatement() {
		StatementImpl statement = new StatementImpl();
		return statement;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public PrintStatement createPrintStatement() {
		PrintStatementImpl printStatement = new PrintStatementImpl();
		return printStatement;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Return createReturn() {
		ReturnImpl return_ = new ReturnImpl();
		return return_;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public IfStatement createIfStatement() {
		IfStatementImpl ifStatement = new IfStatementImpl();
		return ifStatement;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public WhileStatement createWhileStatement() {
		WhileStatementImpl whileStatement = new WhileStatementImpl();
		return whileStatement;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ForStatement createForStatement() {
		ForStatementImpl forStatement = new ForStatementImpl();
		return forStatement;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public TypeRef createTypeRef() {
		TypeRefImpl typeRef = new TypeRefImpl();
		return typeRef;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public SingleTypeRef createSingleTypeRef() {
		SingleTypeRefImpl singleTypeRef = new SingleTypeRefImpl();
		return singleTypeRef;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ClassRef createClassRef() {
		ClassRefImpl classRef = new ClassRefImpl();
		return classRef;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NamedElement createNamedElement() {
		NamedElementImpl namedElement = new NamedElementImpl();
		return namedElement;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public TypedDeclaration createTypedDeclaration() {
		TypedDeclarationImpl typedDeclaration = new TypedDeclarationImpl();
		return typedDeclaration;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Symbol createSymbol() {
		SymbolImpl symbol = new SymbolImpl();
		return symbol;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public VariableDeclaration createVariableDeclaration() {
		VariableDeclarationImpl variableDeclaration = new VariableDeclarationImpl();
		return variableDeclaration;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Assignment createAssignment() {
		AssignmentImpl assignment = new AssignmentImpl();
		return assignment;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Assignee createAssignee() {
		AssigneeImpl assignee = new AssigneeImpl();
		return assignee;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Expression createExpression() {
		ExpressionImpl expression = new ExpressionImpl();
		return expression;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ArrayTypeRef createArrayTypeRef() {
		ArrayTypeRefImpl arrayTypeRef = new ArrayTypeRefImpl();
		return arrayTypeRef;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public IntegerTypeRef createIntegerTypeRef() {
		IntegerTypeRefImpl integerTypeRef = new IntegerTypeRefImpl();
		return integerTypeRef;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public BooleanTypeRef createBooleanTypeRef() {
		BooleanTypeRefImpl booleanTypeRef = new BooleanTypeRefImpl();
		return booleanTypeRef;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public StringTypeRef createStringTypeRef() {
		StringTypeRefImpl stringTypeRef = new StringTypeRefImpl();
		return stringTypeRef;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public VoidTypeRef createVoidTypeRef() {
		VoidTypeRefImpl voidTypeRef = new VoidTypeRefImpl();
		return voidTypeRef;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Or createOr() {
		OrImpl or = new OrImpl();
		return or;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public And createAnd() {
		AndImpl and = new AndImpl();
		return and;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Equality createEquality() {
		EqualityImpl equality = new EqualityImpl();
		return equality;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Inequality createInequality() {
		InequalityImpl inequality = new InequalityImpl();
		return inequality;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public SuperiorOrEqual createSuperiorOrEqual() {
		SuperiorOrEqualImpl superiorOrEqual = new SuperiorOrEqualImpl();
		return superiorOrEqual;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public InferiorOrEqual createInferiorOrEqual() {
		InferiorOrEqualImpl inferiorOrEqual = new InferiorOrEqualImpl();
		return inferiorOrEqual;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Superior createSuperior() {
		SuperiorImpl superior = new SuperiorImpl();
		return superior;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Inferior createInferior() {
		InferiorImpl inferior = new InferiorImpl();
		return inferior;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Plus createPlus() {
		PlusImpl plus = new PlusImpl();
		return plus;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Minus createMinus() {
		MinusImpl minus = new MinusImpl();
		return minus;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Multiplication createMultiplication() {
		MultiplicationImpl multiplication = new MultiplicationImpl();
		return multiplication;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Division createDivision() {
		DivisionImpl division = new DivisionImpl();
		return division;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ArrayAccess createArrayAccess() {
		ArrayAccessImpl arrayAccess = new ArrayAccessImpl();
		return arrayAccess;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ArrayLength createArrayLength() {
		ArrayLengthImpl arrayLength = new ArrayLengthImpl();
		return arrayLength;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Not createNot() {
		NotImpl not = new NotImpl();
		return not;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Neg createNeg() {
		NegImpl neg = new NegImpl();
		return neg;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public FieldAccess createFieldAccess() {
		FieldAccessImpl fieldAccess = new FieldAccessImpl();
		return fieldAccess;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public MethodCall createMethodCall() {
		MethodCallImpl methodCall = new MethodCallImpl();
		return methodCall;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public StringConstant createStringConstant() {
		StringConstantImpl stringConstant = new StringConstantImpl();
		return stringConstant;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public IntConstant createIntConstant() {
		IntConstantImpl intConstant = new IntConstantImpl();
		return intConstant;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public BoolConstant createBoolConstant() {
		BoolConstantImpl boolConstant = new BoolConstantImpl();
		return boolConstant;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public This createThis() {
		ThisImpl this_ = new ThisImpl();
		return this_;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Super createSuper() {
		SuperImpl super_ = new SuperImpl();
		return super_;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Null createNull() {
		NullImpl null_ = new NullImpl();
		return null_;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NewObject createNewObject() {
		NewObjectImpl newObject = new NewObjectImpl();
		return newObject;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NewArray createNewArray() {
		NewArrayImpl newArray = new NewArrayImpl();
		return newArray;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public SymbolRef createSymbolRef() {
		SymbolRefImpl symbolRef = new SymbolRefImpl();
		return symbolRef;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public AccessLevel createAccessLevelFromString(EDataType eDataType, String initialValue) {
		AccessLevel result = AccessLevel.get(initialValue);
		if (result == null) throw new IllegalArgumentException("The value '" + initialValue + "' is not a valid enumerator of '" + eDataType.getName() + "'");
		return result;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String convertAccessLevelToString(EDataType eDataType, Object instanceValue) {
		return instanceValue == null ? null : instanceValue.toString();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public MiniJavaPackage getMiniJavaPackage() {
		return (MiniJavaPackage)getEPackage();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @deprecated
	 * @generated
	 */
	@Deprecated
	public static MiniJavaPackage getPackage() {
		return MiniJavaPackage.eINSTANCE;
	}

} //MiniJavaFactoryImpl
