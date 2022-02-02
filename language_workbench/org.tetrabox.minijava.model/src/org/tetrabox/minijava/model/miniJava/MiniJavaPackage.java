/**
 */
package org.tetrabox.minijava.model.miniJava;

import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EEnum;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.EReference;

/**
 * <!-- begin-user-doc -->
 * The <b>Package</b> for the model.
 * It contains accessors for the meta objects to represent
 * <ul>
 *   <li>each class,</li>
 *   <li>each feature of each class,</li>
 *   <li>each operation of each class,</li>
 *   <li>each enum,</li>
 *   <li>and each data type</li>
 * </ul>
 * <!-- end-user-doc -->
 * @see org.tetrabox.minijava.model.miniJava.MiniJavaFactory
 * @model kind="package"
 * @generated
 */
public interface MiniJavaPackage extends EPackage {
	/**
	 * The package name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNAME = "miniJava";

	/**
	 * The package namespace URI.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNS_URI = "http://org.tetrabox.minijava.xminijava/miniJava/";

	/**
	 * The package namespace name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNS_PREFIX = "miniJava";

	/**
	 * The singleton instance of the package.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	MiniJavaPackage eINSTANCE = org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl.init();

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ProgramImpl <em>Program</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ProgramImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getProgram()
	 * @generated
	 */
	int PROGRAM = 0;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROGRAM__NAME = 0;

	/**
	 * The feature id for the '<em><b>Imports</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROGRAM__IMPORTS = 1;

	/**
	 * The feature id for the '<em><b>Classes</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROGRAM__CLASSES = 2;

	/**
	 * The feature id for the '<em><b>State</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROGRAM__STATE = 3;

	/**
	 * The number of structural features of the '<em>Program</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROGRAM_FEATURE_COUNT = 4;

	/**
	 * The number of operations of the '<em>Program</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROGRAM_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ImportImpl <em>Import</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ImportImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getImport()
	 * @generated
	 */
	int IMPORT = 1;

	/**
	 * The feature id for the '<em><b>Imported Namespace</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IMPORT__IMPORTED_NAMESPACE = 0;

	/**
	 * The number of structural features of the '<em>Import</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IMPORT_FEATURE_COUNT = 1;

	/**
	 * The number of operations of the '<em>Import</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IMPORT_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.NamedElementImpl <em>Named Element</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.NamedElementImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNamedElement()
	 * @generated
	 */
	int NAMED_ELEMENT = 19;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NAMED_ELEMENT__NAME = 0;

	/**
	 * The number of structural features of the '<em>Named Element</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NAMED_ELEMENT_FEATURE_COUNT = 1;

	/**
	 * The number of operations of the '<em>Named Element</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NAMED_ELEMENT_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.TypeDeclarationImpl <em>Type Declaration</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.TypeDeclarationImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getTypeDeclaration()
	 * @generated
	 */
	int TYPE_DECLARATION = 2;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPE_DECLARATION__NAME = NAMED_ELEMENT__NAME;

	/**
	 * The feature id for the '<em><b>Access Level</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPE_DECLARATION__ACCESS_LEVEL = NAMED_ELEMENT_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Implements</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPE_DECLARATION__IMPLEMENTS = NAMED_ELEMENT_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Members</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPE_DECLARATION__MEMBERS = NAMED_ELEMENT_FEATURE_COUNT + 2;

	/**
	 * The number of structural features of the '<em>Type Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPE_DECLARATION_FEATURE_COUNT = NAMED_ELEMENT_FEATURE_COUNT + 3;

	/**
	 * The number of operations of the '<em>Type Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPE_DECLARATION_OPERATION_COUNT = NAMED_ELEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ClassImpl <em>Class</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ClassImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getClass_()
	 * @generated
	 */
	int CLASS = 3;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__NAME = TYPE_DECLARATION__NAME;

	/**
	 * The feature id for the '<em><b>Access Level</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__ACCESS_LEVEL = TYPE_DECLARATION__ACCESS_LEVEL;

	/**
	 * The feature id for the '<em><b>Implements</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__IMPLEMENTS = TYPE_DECLARATION__IMPLEMENTS;

	/**
	 * The feature id for the '<em><b>Members</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__MEMBERS = TYPE_DECLARATION__MEMBERS;

	/**
	 * The feature id for the '<em><b>Abstract</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__ABSTRACT = TYPE_DECLARATION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Super Class</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS__SUPER_CLASS = TYPE_DECLARATION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Class</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS_FEATURE_COUNT = TYPE_DECLARATION_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Class</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS_OPERATION_COUNT = TYPE_DECLARATION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.InterfaceImpl <em>Interface</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.InterfaceImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getInterface()
	 * @generated
	 */
	int INTERFACE = 4;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTERFACE__NAME = TYPE_DECLARATION__NAME;

	/**
	 * The feature id for the '<em><b>Access Level</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTERFACE__ACCESS_LEVEL = TYPE_DECLARATION__ACCESS_LEVEL;

	/**
	 * The feature id for the '<em><b>Implements</b></em>' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTERFACE__IMPLEMENTS = TYPE_DECLARATION__IMPLEMENTS;

	/**
	 * The feature id for the '<em><b>Members</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTERFACE__MEMBERS = TYPE_DECLARATION__MEMBERS;

	/**
	 * The number of structural features of the '<em>Interface</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTERFACE_FEATURE_COUNT = TYPE_DECLARATION_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Interface</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTERFACE_OPERATION_COUNT = TYPE_DECLARATION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.TypedDeclarationImpl <em>Typed Declaration</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.TypedDeclarationImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getTypedDeclaration()
	 * @generated
	 */
	int TYPED_DECLARATION = 20;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPED_DECLARATION__NAME = NAMED_ELEMENT__NAME;

	/**
	 * The feature id for the '<em><b>Type Ref</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPED_DECLARATION__TYPE_REF = NAMED_ELEMENT_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Typed Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPED_DECLARATION_FEATURE_COUNT = NAMED_ELEMENT_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Typed Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPED_DECLARATION_OPERATION_COUNT = NAMED_ELEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.MemberImpl <em>Member</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.MemberImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getMember()
	 * @generated
	 */
	int MEMBER = 5;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MEMBER__NAME = TYPED_DECLARATION__NAME;

	/**
	 * The feature id for the '<em><b>Type Ref</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MEMBER__TYPE_REF = TYPED_DECLARATION__TYPE_REF;

	/**
	 * The feature id for the '<em><b>Access</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MEMBER__ACCESS = TYPED_DECLARATION_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Member</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MEMBER_FEATURE_COUNT = TYPED_DECLARATION_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Member</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MEMBER_OPERATION_COUNT = TYPED_DECLARATION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.MethodImpl <em>Method</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.MethodImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getMethod()
	 * @generated
	 */
	int METHOD = 6;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD__NAME = MEMBER__NAME;

	/**
	 * The feature id for the '<em><b>Type Ref</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD__TYPE_REF = MEMBER__TYPE_REF;

	/**
	 * The feature id for the '<em><b>Access</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD__ACCESS = MEMBER__ACCESS;

	/**
	 * The feature id for the '<em><b>Abstract</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD__ABSTRACT = MEMBER_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Static</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD__STATIC = MEMBER_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Params</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD__PARAMS = MEMBER_FEATURE_COUNT + 2;

	/**
	 * The feature id for the '<em><b>Body</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD__BODY = MEMBER_FEATURE_COUNT + 3;

	/**
	 * The number of structural features of the '<em>Method</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD_FEATURE_COUNT = MEMBER_FEATURE_COUNT + 4;

	/**
	 * The number of operations of the '<em>Method</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD_OPERATION_COUNT = MEMBER_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.SymbolImpl <em>Symbol</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.SymbolImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSymbol()
	 * @generated
	 */
	int SYMBOL = 21;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SYMBOL__NAME = TYPED_DECLARATION__NAME;

	/**
	 * The feature id for the '<em><b>Type Ref</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SYMBOL__TYPE_REF = TYPED_DECLARATION__TYPE_REF;

	/**
	 * The number of structural features of the '<em>Symbol</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SYMBOL_FEATURE_COUNT = TYPED_DECLARATION_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Symbol</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SYMBOL_OPERATION_COUNT = TYPED_DECLARATION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ParameterImpl <em>Parameter</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ParameterImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getParameter()
	 * @generated
	 */
	int PARAMETER = 7;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PARAMETER__NAME = SYMBOL__NAME;

	/**
	 * The feature id for the '<em><b>Type Ref</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PARAMETER__TYPE_REF = SYMBOL__TYPE_REF;

	/**
	 * The number of structural features of the '<em>Parameter</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PARAMETER_FEATURE_COUNT = SYMBOL_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Parameter</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PARAMETER_OPERATION_COUNT = SYMBOL_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.FieldImpl <em>Field</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.FieldImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getField()
	 * @generated
	 */
	int FIELD = 8;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD__NAME = MEMBER__NAME;

	/**
	 * The feature id for the '<em><b>Type Ref</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD__TYPE_REF = MEMBER__TYPE_REF;

	/**
	 * The feature id for the '<em><b>Access</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD__ACCESS = MEMBER__ACCESS;

	/**
	 * The feature id for the '<em><b>Default Value</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD__DEFAULT_VALUE = MEMBER_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Field</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD_FEATURE_COUNT = MEMBER_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Field</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD_OPERATION_COUNT = MEMBER_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.StatementImpl <em>Statement</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.StatementImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getStatement()
	 * @generated
	 */
	int STATEMENT = 10;

	/**
	 * The number of structural features of the '<em>Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATEMENT_FEATURE_COUNT = 0;

	/**
	 * The number of operations of the '<em>Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STATEMENT_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.BlockImpl <em>Block</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.BlockImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getBlock()
	 * @generated
	 */
	int BLOCK = 9;

	/**
	 * The feature id for the '<em><b>Statements</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BLOCK__STATEMENTS = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Block</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BLOCK_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Block</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BLOCK_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.PrintStatementImpl <em>Print Statement</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.PrintStatementImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getPrintStatement()
	 * @generated
	 */
	int PRINT_STATEMENT = 11;

	/**
	 * The feature id for the '<em><b>Expression</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PRINT_STATEMENT__EXPRESSION = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Print Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PRINT_STATEMENT_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Print Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PRINT_STATEMENT_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ReturnImpl <em>Return</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ReturnImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getReturn()
	 * @generated
	 */
	int RETURN = 12;

	/**
	 * The feature id for the '<em><b>Expression</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RETURN__EXPRESSION = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Return</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RETURN_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Return</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int RETURN_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.IfStatementImpl <em>If Statement</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.IfStatementImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getIfStatement()
	 * @generated
	 */
	int IF_STATEMENT = 13;

	/**
	 * The feature id for the '<em><b>Expression</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IF_STATEMENT__EXPRESSION = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Then Block</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IF_STATEMENT__THEN_BLOCK = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Else Block</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IF_STATEMENT__ELSE_BLOCK = STATEMENT_FEATURE_COUNT + 2;

	/**
	 * The number of structural features of the '<em>If Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IF_STATEMENT_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 3;

	/**
	 * The number of operations of the '<em>If Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int IF_STATEMENT_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.WhileStatementImpl <em>While Statement</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.WhileStatementImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getWhileStatement()
	 * @generated
	 */
	int WHILE_STATEMENT = 14;

	/**
	 * The feature id for the '<em><b>Condition</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int WHILE_STATEMENT__CONDITION = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Block</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int WHILE_STATEMENT__BLOCK = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>While Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int WHILE_STATEMENT_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>While Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int WHILE_STATEMENT_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ForStatementImpl <em>For Statement</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ForStatementImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getForStatement()
	 * @generated
	 */
	int FOR_STATEMENT = 15;

	/**
	 * The feature id for the '<em><b>Declaration</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FOR_STATEMENT__DECLARATION = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Condition</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FOR_STATEMENT__CONDITION = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Progression</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FOR_STATEMENT__PROGRESSION = STATEMENT_FEATURE_COUNT + 2;

	/**
	 * The feature id for the '<em><b>Block</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FOR_STATEMENT__BLOCK = STATEMENT_FEATURE_COUNT + 3;

	/**
	 * The number of structural features of the '<em>For Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FOR_STATEMENT_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 4;

	/**
	 * The number of operations of the '<em>For Statement</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FOR_STATEMENT_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.TypeRefImpl <em>Type Ref</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.TypeRefImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getTypeRef()
	 * @generated
	 */
	int TYPE_REF = 16;

	/**
	 * The number of structural features of the '<em>Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPE_REF_FEATURE_COUNT = 0;

	/**
	 * The number of operations of the '<em>Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int TYPE_REF_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.SingleTypeRefImpl <em>Single Type Ref</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.SingleTypeRefImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSingleTypeRef()
	 * @generated
	 */
	int SINGLE_TYPE_REF = 17;

	/**
	 * The number of structural features of the '<em>Single Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_TYPE_REF_FEATURE_COUNT = TYPE_REF_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Single Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SINGLE_TYPE_REF_OPERATION_COUNT = TYPE_REF_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ClassRefImpl <em>Class Ref</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ClassRefImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getClassRef()
	 * @generated
	 */
	int CLASS_REF = 18;

	/**
	 * The feature id for the '<em><b>Referenced Class</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS_REF__REFERENCED_CLASS = SINGLE_TYPE_REF_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Class Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS_REF_FEATURE_COUNT = SINGLE_TYPE_REF_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Class Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int CLASS_REF_OPERATION_COUNT = SINGLE_TYPE_REF_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.VariableDeclarationImpl <em>Variable Declaration</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.VariableDeclarationImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getVariableDeclaration()
	 * @generated
	 */
	int VARIABLE_DECLARATION = 22;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VARIABLE_DECLARATION__NAME = SYMBOL__NAME;

	/**
	 * The feature id for the '<em><b>Type Ref</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VARIABLE_DECLARATION__TYPE_REF = SYMBOL__TYPE_REF;

	/**
	 * The number of structural features of the '<em>Variable Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VARIABLE_DECLARATION_FEATURE_COUNT = SYMBOL_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Variable Declaration</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VARIABLE_DECLARATION_OPERATION_COUNT = SYMBOL_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.AssignmentImpl <em>Assignment</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.AssignmentImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getAssignment()
	 * @generated
	 */
	int ASSIGNMENT = 23;

	/**
	 * The feature id for the '<em><b>Assignee</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSIGNMENT__ASSIGNEE = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Value</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSIGNMENT__VALUE = STATEMENT_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Assignment</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSIGNMENT_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Assignment</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSIGNMENT_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.AssigneeImpl <em>Assignee</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.AssigneeImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getAssignee()
	 * @generated
	 */
	int ASSIGNEE = 24;

	/**
	 * The number of structural features of the '<em>Assignee</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSIGNEE_FEATURE_COUNT = 0;

	/**
	 * The number of operations of the '<em>Assignee</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ASSIGNEE_OPERATION_COUNT = 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ExpressionImpl <em>Expression</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ExpressionImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getExpression()
	 * @generated
	 */
	int EXPRESSION = 25;

	/**
	 * The number of structural features of the '<em>Expression</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPRESSION_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Expression</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EXPRESSION_OPERATION_COUNT = STATEMENT_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ArrayTypeRefImpl <em>Array Type Ref</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ArrayTypeRefImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getArrayTypeRef()
	 * @generated
	 */
	int ARRAY_TYPE_REF = 26;

	/**
	 * The feature id for the '<em><b>Type Ref</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_TYPE_REF__TYPE_REF = TYPE_REF_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Array Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_TYPE_REF_FEATURE_COUNT = TYPE_REF_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Array Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_TYPE_REF_OPERATION_COUNT = TYPE_REF_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.IntegerTypeRefImpl <em>Integer Type Ref</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.IntegerTypeRefImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getIntegerTypeRef()
	 * @generated
	 */
	int INTEGER_TYPE_REF = 27;

	/**
	 * The number of structural features of the '<em>Integer Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTEGER_TYPE_REF_FEATURE_COUNT = SINGLE_TYPE_REF_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Integer Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INTEGER_TYPE_REF_OPERATION_COUNT = SINGLE_TYPE_REF_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.BooleanTypeRefImpl <em>Boolean Type Ref</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.BooleanTypeRefImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getBooleanTypeRef()
	 * @generated
	 */
	int BOOLEAN_TYPE_REF = 28;

	/**
	 * The number of structural features of the '<em>Boolean Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BOOLEAN_TYPE_REF_FEATURE_COUNT = SINGLE_TYPE_REF_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Boolean Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BOOLEAN_TYPE_REF_OPERATION_COUNT = SINGLE_TYPE_REF_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.StringTypeRefImpl <em>String Type Ref</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.StringTypeRefImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getStringTypeRef()
	 * @generated
	 */
	int STRING_TYPE_REF = 29;

	/**
	 * The number of structural features of the '<em>String Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_TYPE_REF_FEATURE_COUNT = SINGLE_TYPE_REF_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>String Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_TYPE_REF_OPERATION_COUNT = SINGLE_TYPE_REF_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.VoidTypeRefImpl <em>Void Type Ref</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.VoidTypeRefImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getVoidTypeRef()
	 * @generated
	 */
	int VOID_TYPE_REF = 30;

	/**
	 * The number of structural features of the '<em>Void Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VOID_TYPE_REF_FEATURE_COUNT = SINGLE_TYPE_REF_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Void Type Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int VOID_TYPE_REF_OPERATION_COUNT = SINGLE_TYPE_REF_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.OrImpl <em>Or</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.OrImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getOr()
	 * @generated
	 */
	int OR = 31;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OR__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OR__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Or</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OR_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Or</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int OR_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.AndImpl <em>And</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.AndImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getAnd()
	 * @generated
	 */
	int AND = 32;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AND__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AND__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>And</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AND_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>And</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int AND_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.EqualityImpl <em>Equality</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.EqualityImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getEquality()
	 * @generated
	 */
	int EQUALITY = 33;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EQUALITY__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EQUALITY__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Equality</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EQUALITY_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Equality</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int EQUALITY_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.InequalityImpl <em>Inequality</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.InequalityImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getInequality()
	 * @generated
	 */
	int INEQUALITY = 34;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INEQUALITY__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INEQUALITY__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Inequality</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INEQUALITY_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Inequality</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INEQUALITY_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.SuperiorOrEqualImpl <em>Superior Or Equal</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.SuperiorOrEqualImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSuperiorOrEqual()
	 * @generated
	 */
	int SUPERIOR_OR_EQUAL = 35;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPERIOR_OR_EQUAL__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPERIOR_OR_EQUAL__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Superior Or Equal</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPERIOR_OR_EQUAL_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Superior Or Equal</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPERIOR_OR_EQUAL_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.InferiorOrEqualImpl <em>Inferior Or Equal</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.InferiorOrEqualImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getInferiorOrEqual()
	 * @generated
	 */
	int INFERIOR_OR_EQUAL = 36;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INFERIOR_OR_EQUAL__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INFERIOR_OR_EQUAL__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Inferior Or Equal</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INFERIOR_OR_EQUAL_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Inferior Or Equal</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INFERIOR_OR_EQUAL_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.SuperiorImpl <em>Superior</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.SuperiorImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSuperior()
	 * @generated
	 */
	int SUPERIOR = 37;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPERIOR__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPERIOR__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Superior</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPERIOR_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Superior</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPERIOR_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.InferiorImpl <em>Inferior</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.InferiorImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getInferior()
	 * @generated
	 */
	int INFERIOR = 38;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INFERIOR__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INFERIOR__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Inferior</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INFERIOR_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Inferior</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INFERIOR_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.PlusImpl <em>Plus</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.PlusImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getPlus()
	 * @generated
	 */
	int PLUS = 39;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PLUS__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PLUS__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Plus</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PLUS_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Plus</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PLUS_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.MinusImpl <em>Minus</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.MinusImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getMinus()
	 * @generated
	 */
	int MINUS = 40;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MINUS__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MINUS__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Minus</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MINUS_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Minus</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MINUS_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.MultiplicationImpl <em>Multiplication</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.MultiplicationImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getMultiplication()
	 * @generated
	 */
	int MULTIPLICATION = 41;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MULTIPLICATION__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MULTIPLICATION__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Multiplication</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MULTIPLICATION_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Multiplication</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int MULTIPLICATION_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.DivisionImpl <em>Division</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.DivisionImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getDivision()
	 * @generated
	 */
	int DIVISION = 42;

	/**
	 * The feature id for the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DIVISION__LEFT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DIVISION__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Division</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DIVISION_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Division</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int DIVISION_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ArrayAccessImpl <em>Array Access</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ArrayAccessImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getArrayAccess()
	 * @generated
	 */
	int ARRAY_ACCESS = 43;

	/**
	 * The feature id for the '<em><b>Object</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_ACCESS__OBJECT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Index</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_ACCESS__INDEX = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Array Access</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_ACCESS_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Array Access</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_ACCESS_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ArrayLengthImpl <em>Array Length</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ArrayLengthImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getArrayLength()
	 * @generated
	 */
	int ARRAY_LENGTH = 44;

	/**
	 * The feature id for the '<em><b>Array</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_LENGTH__ARRAY = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Array Length</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_LENGTH_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Array Length</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int ARRAY_LENGTH_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.NotImpl <em>Not</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.NotImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNot()
	 * @generated
	 */
	int NOT = 45;

	/**
	 * The feature id for the '<em><b>Expression</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NOT__EXPRESSION = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Not</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NOT_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Not</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NOT_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.NegImpl <em>Neg</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.NegImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNeg()
	 * @generated
	 */
	int NEG = 46;

	/**
	 * The feature id for the '<em><b>Expression</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEG__EXPRESSION = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Neg</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEG_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Neg</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEG_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.FieldAccessImpl <em>Field Access</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.FieldAccessImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getFieldAccess()
	 * @generated
	 */
	int FIELD_ACCESS = 47;

	/**
	 * The feature id for the '<em><b>Receiver</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD_ACCESS__RECEIVER = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Field</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD_ACCESS__FIELD = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>Field Access</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD_ACCESS_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>Field Access</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int FIELD_ACCESS_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.MethodCallImpl <em>Method Call</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.MethodCallImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getMethodCall()
	 * @generated
	 */
	int METHOD_CALL = 48;

	/**
	 * The feature id for the '<em><b>Receiver</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD_CALL__RECEIVER = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Method</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD_CALL__METHOD = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The feature id for the '<em><b>Args</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD_CALL__ARGS = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The number of structural features of the '<em>Method Call</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD_CALL_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 3;

	/**
	 * The number of operations of the '<em>Method Call</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int METHOD_CALL_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.StringConstantImpl <em>String Constant</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.StringConstantImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getStringConstant()
	 * @generated
	 */
	int STRING_CONSTANT = 49;

	/**
	 * The feature id for the '<em><b>Value</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_CONSTANT__VALUE = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>String Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_CONSTANT_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>String Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int STRING_CONSTANT_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.IntConstantImpl <em>Int Constant</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.IntConstantImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getIntConstant()
	 * @generated
	 */
	int INT_CONSTANT = 50;

	/**
	 * The feature id for the '<em><b>Value</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INT_CONSTANT__VALUE = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Int Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INT_CONSTANT_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Int Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int INT_CONSTANT_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.BoolConstantImpl <em>Bool Constant</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.BoolConstantImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getBoolConstant()
	 * @generated
	 */
	int BOOL_CONSTANT = 51;

	/**
	 * The feature id for the '<em><b>Value</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BOOL_CONSTANT__VALUE = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Bool Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BOOL_CONSTANT_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Bool Constant</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int BOOL_CONSTANT_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.ThisImpl <em>This</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.ThisImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getThis()
	 * @generated
	 */
	int THIS = 52;

	/**
	 * The number of structural features of the '<em>This</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int THIS_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>This</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int THIS_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.SuperImpl <em>Super</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.SuperImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSuper()
	 * @generated
	 */
	int SUPER = 53;

	/**
	 * The number of structural features of the '<em>Super</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPER_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Super</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SUPER_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.NullImpl <em>Null</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.NullImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNull()
	 * @generated
	 */
	int NULL = 54;

	/**
	 * The number of structural features of the '<em>Null</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NULL_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The number of operations of the '<em>Null</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NULL_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.NewObjectImpl <em>New Object</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.NewObjectImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNewObject()
	 * @generated
	 */
	int NEW_OBJECT = 55;

	/**
	 * The feature id for the '<em><b>Type</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_OBJECT__TYPE = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Args</b></em>' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_OBJECT__ARGS = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>New Object</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_OBJECT_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>New Object</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_OBJECT_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.NewArrayImpl <em>New Array</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.NewArrayImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNewArray()
	 * @generated
	 */
	int NEW_ARRAY = 56;

	/**
	 * The feature id for the '<em><b>Type</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_ARRAY__TYPE = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The feature id for the '<em><b>Size</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_ARRAY__SIZE = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of structural features of the '<em>New Array</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_ARRAY_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

	/**
	 * The number of operations of the '<em>New Array</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int NEW_ARRAY_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.impl.SymbolRefImpl <em>Symbol Ref</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.impl.SymbolRefImpl
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSymbolRef()
	 * @generated
	 */
	int SYMBOL_REF = 57;

	/**
	 * The feature id for the '<em><b>Symbol</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SYMBOL_REF__SYMBOL = EXPRESSION_FEATURE_COUNT + 0;

	/**
	 * The number of structural features of the '<em>Symbol Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SYMBOL_REF_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 1;

	/**
	 * The number of operations of the '<em>Symbol Ref</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int SYMBOL_REF_OPERATION_COUNT = EXPRESSION_OPERATION_COUNT + 0;

	/**
	 * The meta object id for the '{@link org.tetrabox.minijava.model.miniJava.AccessLevel <em>Access Level</em>}' enum.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.tetrabox.minijava.model.miniJava.AccessLevel
	 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getAccessLevel()
	 * @generated
	 */
	int ACCESS_LEVEL = 58;


	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Program <em>Program</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Program</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Program
	 * @generated
	 */
	EClass getProgram();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.Program#getName <em>Name</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Name</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Program#getName()
	 * @see #getProgram()
	 * @generated
	 */
	EAttribute getProgram_Name();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.Program#getImports <em>Imports</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Imports</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Program#getImports()
	 * @see #getProgram()
	 * @generated
	 */
	EReference getProgram_Imports();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.Program#getClasses <em>Classes</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Classes</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Program#getClasses()
	 * @see #getProgram()
	 * @generated
	 */
	EReference getProgram_Classes();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Program#getState <em>State</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>State</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Program#getState()
	 * @see #getProgram()
	 * @generated
	 */
	EReference getProgram_State();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Import <em>Import</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Import</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Import
	 * @generated
	 */
	EClass getImport();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.Import#getImportedNamespace <em>Imported Namespace</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Imported Namespace</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Import#getImportedNamespace()
	 * @see #getImport()
	 * @generated
	 */
	EAttribute getImport_ImportedNamespace();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.TypeDeclaration <em>Type Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Type Declaration</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.TypeDeclaration
	 * @generated
	 */
	EClass getTypeDeclaration();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.TypeDeclaration#getAccessLevel <em>Access Level</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Access Level</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.TypeDeclaration#getAccessLevel()
	 * @see #getTypeDeclaration()
	 * @generated
	 */
	EAttribute getTypeDeclaration_AccessLevel();

	/**
	 * Returns the meta object for the reference list '{@link org.tetrabox.minijava.model.miniJava.TypeDeclaration#getImplements <em>Implements</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference list '<em>Implements</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.TypeDeclaration#getImplements()
	 * @see #getTypeDeclaration()
	 * @generated
	 */
	EReference getTypeDeclaration_Implements();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.TypeDeclaration#getMembers <em>Members</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Members</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.TypeDeclaration#getMembers()
	 * @see #getTypeDeclaration()
	 * @generated
	 */
	EReference getTypeDeclaration_Members();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Class <em>Class</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Class</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Class
	 * @generated
	 */
	EClass getClass_();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.Class#isAbstract <em>Abstract</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Abstract</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Class#isAbstract()
	 * @see #getClass_()
	 * @generated
	 */
	EAttribute getClass_Abstract();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.Class#getSuperClass <em>Super Class</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Super Class</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Class#getSuperClass()
	 * @see #getClass_()
	 * @generated
	 */
	EReference getClass_SuperClass();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Interface <em>Interface</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Interface</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Interface
	 * @generated
	 */
	EClass getInterface();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Member <em>Member</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Member</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Member
	 * @generated
	 */
	EClass getMember();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.Member#getAccess <em>Access</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Access</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Member#getAccess()
	 * @see #getMember()
	 * @generated
	 */
	EAttribute getMember_Access();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Method <em>Method</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Method</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Method
	 * @generated
	 */
	EClass getMethod();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.Method#isAbstract <em>Abstract</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Abstract</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Method#isAbstract()
	 * @see #getMethod()
	 * @generated
	 */
	EAttribute getMethod_Abstract();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.Method#isStatic <em>Static</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Static</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Method#isStatic()
	 * @see #getMethod()
	 * @generated
	 */
	EAttribute getMethod_Static();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.Method#getParams <em>Params</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Params</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Method#getParams()
	 * @see #getMethod()
	 * @generated
	 */
	EReference getMethod_Params();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Method#getBody <em>Body</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Body</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Method#getBody()
	 * @see #getMethod()
	 * @generated
	 */
	EReference getMethod_Body();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Parameter <em>Parameter</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Parameter</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Parameter
	 * @generated
	 */
	EClass getParameter();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Field <em>Field</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Field</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Field
	 * @generated
	 */
	EClass getField();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Field#getDefaultValue <em>Default Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Default Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Field#getDefaultValue()
	 * @see #getField()
	 * @generated
	 */
	EReference getField_DefaultValue();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Block <em>Block</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Block</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Block
	 * @generated
	 */
	EClass getBlock();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.Block#getStatements <em>Statements</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Statements</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Block#getStatements()
	 * @see #getBlock()
	 * @generated
	 */
	EReference getBlock_Statements();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Statement <em>Statement</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Statement</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Statement
	 * @generated
	 */
	EClass getStatement();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.PrintStatement <em>Print Statement</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Print Statement</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.PrintStatement
	 * @generated
	 */
	EClass getPrintStatement();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.PrintStatement#getExpression <em>Expression</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Expression</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.PrintStatement#getExpression()
	 * @see #getPrintStatement()
	 * @generated
	 */
	EReference getPrintStatement_Expression();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Return <em>Return</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Return</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Return
	 * @generated
	 */
	EClass getReturn();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Return#getExpression <em>Expression</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Expression</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Return#getExpression()
	 * @see #getReturn()
	 * @generated
	 */
	EReference getReturn_Expression();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.IfStatement <em>If Statement</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>If Statement</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.IfStatement
	 * @generated
	 */
	EClass getIfStatement();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.IfStatement#getExpression <em>Expression</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Expression</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.IfStatement#getExpression()
	 * @see #getIfStatement()
	 * @generated
	 */
	EReference getIfStatement_Expression();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.IfStatement#getThenBlock <em>Then Block</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Then Block</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.IfStatement#getThenBlock()
	 * @see #getIfStatement()
	 * @generated
	 */
	EReference getIfStatement_ThenBlock();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.IfStatement#getElseBlock <em>Else Block</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Else Block</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.IfStatement#getElseBlock()
	 * @see #getIfStatement()
	 * @generated
	 */
	EReference getIfStatement_ElseBlock();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.WhileStatement <em>While Statement</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>While Statement</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.WhileStatement
	 * @generated
	 */
	EClass getWhileStatement();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.WhileStatement#getCondition <em>Condition</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Condition</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.WhileStatement#getCondition()
	 * @see #getWhileStatement()
	 * @generated
	 */
	EReference getWhileStatement_Condition();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.WhileStatement#getBlock <em>Block</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Block</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.WhileStatement#getBlock()
	 * @see #getWhileStatement()
	 * @generated
	 */
	EReference getWhileStatement_Block();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.ForStatement <em>For Statement</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>For Statement</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ForStatement
	 * @generated
	 */
	EClass getForStatement();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.ForStatement#getDeclaration <em>Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Declaration</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ForStatement#getDeclaration()
	 * @see #getForStatement()
	 * @generated
	 */
	EReference getForStatement_Declaration();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.ForStatement#getCondition <em>Condition</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Condition</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ForStatement#getCondition()
	 * @see #getForStatement()
	 * @generated
	 */
	EReference getForStatement_Condition();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.ForStatement#getProgression <em>Progression</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Progression</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ForStatement#getProgression()
	 * @see #getForStatement()
	 * @generated
	 */
	EReference getForStatement_Progression();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.ForStatement#getBlock <em>Block</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Block</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ForStatement#getBlock()
	 * @see #getForStatement()
	 * @generated
	 */
	EReference getForStatement_Block();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.TypeRef <em>Type Ref</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Type Ref</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.TypeRef
	 * @generated
	 */
	EClass getTypeRef();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.SingleTypeRef <em>Single Type Ref</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Single Type Ref</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.SingleTypeRef
	 * @generated
	 */
	EClass getSingleTypeRef();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.ClassRef <em>Class Ref</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Class Ref</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ClassRef
	 * @generated
	 */
	EClass getClassRef();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.ClassRef#getReferencedClass <em>Referenced Class</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Referenced Class</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ClassRef#getReferencedClass()
	 * @see #getClassRef()
	 * @generated
	 */
	EReference getClassRef_ReferencedClass();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.NamedElement <em>Named Element</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Named Element</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.NamedElement
	 * @generated
	 */
	EClass getNamedElement();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.NamedElement#getName <em>Name</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Name</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.NamedElement#getName()
	 * @see #getNamedElement()
	 * @generated
	 */
	EAttribute getNamedElement_Name();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.TypedDeclaration <em>Typed Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Typed Declaration</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.TypedDeclaration
	 * @generated
	 */
	EClass getTypedDeclaration();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.TypedDeclaration#getTypeRef <em>Type Ref</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Type Ref</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.TypedDeclaration#getTypeRef()
	 * @see #getTypedDeclaration()
	 * @generated
	 */
	EReference getTypedDeclaration_TypeRef();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Symbol <em>Symbol</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Symbol</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Symbol
	 * @generated
	 */
	EClass getSymbol();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.VariableDeclaration <em>Variable Declaration</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Variable Declaration</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.VariableDeclaration
	 * @generated
	 */
	EClass getVariableDeclaration();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Assignment <em>Assignment</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Assignment</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Assignment
	 * @generated
	 */
	EClass getAssignment();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Assignment#getAssignee <em>Assignee</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Assignee</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Assignment#getAssignee()
	 * @see #getAssignment()
	 * @generated
	 */
	EReference getAssignment_Assignee();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Assignment#getValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Assignment#getValue()
	 * @see #getAssignment()
	 * @generated
	 */
	EReference getAssignment_Value();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Assignee <em>Assignee</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Assignee</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Assignee
	 * @generated
	 */
	EClass getAssignee();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Expression <em>Expression</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Expression</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Expression
	 * @generated
	 */
	EClass getExpression();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.ArrayTypeRef <em>Array Type Ref</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Array Type Ref</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ArrayTypeRef
	 * @generated
	 */
	EClass getArrayTypeRef();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.ArrayTypeRef#getTypeRef <em>Type Ref</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Type Ref</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ArrayTypeRef#getTypeRef()
	 * @see #getArrayTypeRef()
	 * @generated
	 */
	EReference getArrayTypeRef_TypeRef();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.IntegerTypeRef <em>Integer Type Ref</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Integer Type Ref</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.IntegerTypeRef
	 * @generated
	 */
	EClass getIntegerTypeRef();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.BooleanTypeRef <em>Boolean Type Ref</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Boolean Type Ref</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.BooleanTypeRef
	 * @generated
	 */
	EClass getBooleanTypeRef();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.StringTypeRef <em>String Type Ref</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>String Type Ref</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.StringTypeRef
	 * @generated
	 */
	EClass getStringTypeRef();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.VoidTypeRef <em>Void Type Ref</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Void Type Ref</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.VoidTypeRef
	 * @generated
	 */
	EClass getVoidTypeRef();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Or <em>Or</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Or</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Or
	 * @generated
	 */
	EClass getOr();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Or#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Or#getLeft()
	 * @see #getOr()
	 * @generated
	 */
	EReference getOr_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Or#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Or#getRight()
	 * @see #getOr()
	 * @generated
	 */
	EReference getOr_Right();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.And <em>And</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>And</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.And
	 * @generated
	 */
	EClass getAnd();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.And#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.And#getLeft()
	 * @see #getAnd()
	 * @generated
	 */
	EReference getAnd_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.And#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.And#getRight()
	 * @see #getAnd()
	 * @generated
	 */
	EReference getAnd_Right();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Equality <em>Equality</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Equality</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Equality
	 * @generated
	 */
	EClass getEquality();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Equality#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Equality#getLeft()
	 * @see #getEquality()
	 * @generated
	 */
	EReference getEquality_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Equality#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Equality#getRight()
	 * @see #getEquality()
	 * @generated
	 */
	EReference getEquality_Right();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Inequality <em>Inequality</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Inequality</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Inequality
	 * @generated
	 */
	EClass getInequality();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Inequality#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Inequality#getLeft()
	 * @see #getInequality()
	 * @generated
	 */
	EReference getInequality_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Inequality#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Inequality#getRight()
	 * @see #getInequality()
	 * @generated
	 */
	EReference getInequality_Right();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.SuperiorOrEqual <em>Superior Or Equal</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Superior Or Equal</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.SuperiorOrEqual
	 * @generated
	 */
	EClass getSuperiorOrEqual();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.SuperiorOrEqual#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.SuperiorOrEqual#getLeft()
	 * @see #getSuperiorOrEqual()
	 * @generated
	 */
	EReference getSuperiorOrEqual_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.SuperiorOrEqual#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.SuperiorOrEqual#getRight()
	 * @see #getSuperiorOrEqual()
	 * @generated
	 */
	EReference getSuperiorOrEqual_Right();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.InferiorOrEqual <em>Inferior Or Equal</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Inferior Or Equal</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.InferiorOrEqual
	 * @generated
	 */
	EClass getInferiorOrEqual();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.InferiorOrEqual#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.InferiorOrEqual#getLeft()
	 * @see #getInferiorOrEqual()
	 * @generated
	 */
	EReference getInferiorOrEqual_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.InferiorOrEqual#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.InferiorOrEqual#getRight()
	 * @see #getInferiorOrEqual()
	 * @generated
	 */
	EReference getInferiorOrEqual_Right();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Superior <em>Superior</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Superior</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Superior
	 * @generated
	 */
	EClass getSuperior();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Superior#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Superior#getLeft()
	 * @see #getSuperior()
	 * @generated
	 */
	EReference getSuperior_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Superior#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Superior#getRight()
	 * @see #getSuperior()
	 * @generated
	 */
	EReference getSuperior_Right();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Inferior <em>Inferior</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Inferior</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Inferior
	 * @generated
	 */
	EClass getInferior();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Inferior#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Inferior#getLeft()
	 * @see #getInferior()
	 * @generated
	 */
	EReference getInferior_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Inferior#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Inferior#getRight()
	 * @see #getInferior()
	 * @generated
	 */
	EReference getInferior_Right();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Plus <em>Plus</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Plus</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Plus
	 * @generated
	 */
	EClass getPlus();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Plus#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Plus#getLeft()
	 * @see #getPlus()
	 * @generated
	 */
	EReference getPlus_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Plus#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Plus#getRight()
	 * @see #getPlus()
	 * @generated
	 */
	EReference getPlus_Right();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Minus <em>Minus</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Minus</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Minus
	 * @generated
	 */
	EClass getMinus();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Minus#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Minus#getLeft()
	 * @see #getMinus()
	 * @generated
	 */
	EReference getMinus_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Minus#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Minus#getRight()
	 * @see #getMinus()
	 * @generated
	 */
	EReference getMinus_Right();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Multiplication <em>Multiplication</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Multiplication</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Multiplication
	 * @generated
	 */
	EClass getMultiplication();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Multiplication#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Multiplication#getLeft()
	 * @see #getMultiplication()
	 * @generated
	 */
	EReference getMultiplication_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Multiplication#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Multiplication#getRight()
	 * @see #getMultiplication()
	 * @generated
	 */
	EReference getMultiplication_Right();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Division <em>Division</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Division</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Division
	 * @generated
	 */
	EClass getDivision();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Division#getLeft <em>Left</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Left</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Division#getLeft()
	 * @see #getDivision()
	 * @generated
	 */
	EReference getDivision_Left();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Division#getRight <em>Right</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Right</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Division#getRight()
	 * @see #getDivision()
	 * @generated
	 */
	EReference getDivision_Right();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.ArrayAccess <em>Array Access</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Array Access</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ArrayAccess
	 * @generated
	 */
	EClass getArrayAccess();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.ArrayAccess#getObject <em>Object</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Object</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ArrayAccess#getObject()
	 * @see #getArrayAccess()
	 * @generated
	 */
	EReference getArrayAccess_Object();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.ArrayAccess#getIndex <em>Index</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Index</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ArrayAccess#getIndex()
	 * @see #getArrayAccess()
	 * @generated
	 */
	EReference getArrayAccess_Index();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.ArrayLength <em>Array Length</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Array Length</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ArrayLength
	 * @generated
	 */
	EClass getArrayLength();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.ArrayLength#getArray <em>Array</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Array</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.ArrayLength#getArray()
	 * @see #getArrayLength()
	 * @generated
	 */
	EReference getArrayLength_Array();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Not <em>Not</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Not</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Not
	 * @generated
	 */
	EClass getNot();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Not#getExpression <em>Expression</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Expression</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Not#getExpression()
	 * @see #getNot()
	 * @generated
	 */
	EReference getNot_Expression();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Neg <em>Neg</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Neg</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Neg
	 * @generated
	 */
	EClass getNeg();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.Neg#getExpression <em>Expression</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Expression</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Neg#getExpression()
	 * @see #getNeg()
	 * @generated
	 */
	EReference getNeg_Expression();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.FieldAccess <em>Field Access</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Field Access</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.FieldAccess
	 * @generated
	 */
	EClass getFieldAccess();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.FieldAccess#getReceiver <em>Receiver</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Receiver</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.FieldAccess#getReceiver()
	 * @see #getFieldAccess()
	 * @generated
	 */
	EReference getFieldAccess_Receiver();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.FieldAccess#getField <em>Field</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Field</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.FieldAccess#getField()
	 * @see #getFieldAccess()
	 * @generated
	 */
	EReference getFieldAccess_Field();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.MethodCall <em>Method Call</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Method Call</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.MethodCall
	 * @generated
	 */
	EClass getMethodCall();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.MethodCall#getReceiver <em>Receiver</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Receiver</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.MethodCall#getReceiver()
	 * @see #getMethodCall()
	 * @generated
	 */
	EReference getMethodCall_Receiver();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.MethodCall#getMethod <em>Method</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Method</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.MethodCall#getMethod()
	 * @see #getMethodCall()
	 * @generated
	 */
	EReference getMethodCall_Method();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.MethodCall#getArgs <em>Args</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Args</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.MethodCall#getArgs()
	 * @see #getMethodCall()
	 * @generated
	 */
	EReference getMethodCall_Args();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.StringConstant <em>String Constant</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>String Constant</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.StringConstant
	 * @generated
	 */
	EClass getStringConstant();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.StringConstant#getValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.StringConstant#getValue()
	 * @see #getStringConstant()
	 * @generated
	 */
	EAttribute getStringConstant_Value();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.IntConstant <em>Int Constant</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Int Constant</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.IntConstant
	 * @generated
	 */
	EClass getIntConstant();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.IntConstant#getValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.IntConstant#getValue()
	 * @see #getIntConstant()
	 * @generated
	 */
	EAttribute getIntConstant_Value();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.BoolConstant <em>Bool Constant</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Bool Constant</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.BoolConstant
	 * @generated
	 */
	EClass getBoolConstant();

	/**
	 * Returns the meta object for the attribute '{@link org.tetrabox.minijava.model.miniJava.BoolConstant#getValue <em>Value</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Value</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.BoolConstant#getValue()
	 * @see #getBoolConstant()
	 * @generated
	 */
	EAttribute getBoolConstant_Value();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.This <em>This</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>This</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.This
	 * @generated
	 */
	EClass getThis();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Super <em>Super</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Super</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Super
	 * @generated
	 */
	EClass getSuper();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.Null <em>Null</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Null</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.Null
	 * @generated
	 */
	EClass getNull();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.NewObject <em>New Object</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>New Object</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.NewObject
	 * @generated
	 */
	EClass getNewObject();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.NewObject#getType <em>Type</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Type</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.NewObject#getType()
	 * @see #getNewObject()
	 * @generated
	 */
	EReference getNewObject_Type();

	/**
	 * Returns the meta object for the containment reference list '{@link org.tetrabox.minijava.model.miniJava.NewObject#getArgs <em>Args</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference list '<em>Args</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.NewObject#getArgs()
	 * @see #getNewObject()
	 * @generated
	 */
	EReference getNewObject_Args();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.NewArray <em>New Array</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>New Array</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.NewArray
	 * @generated
	 */
	EClass getNewArray();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.NewArray#getType <em>Type</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Type</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.NewArray#getType()
	 * @see #getNewArray()
	 * @generated
	 */
	EReference getNewArray_Type();

	/**
	 * Returns the meta object for the containment reference '{@link org.tetrabox.minijava.model.miniJava.NewArray#getSize <em>Size</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the containment reference '<em>Size</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.NewArray#getSize()
	 * @see #getNewArray()
	 * @generated
	 */
	EReference getNewArray_Size();

	/**
	 * Returns the meta object for class '{@link org.tetrabox.minijava.model.miniJava.SymbolRef <em>Symbol Ref</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Symbol Ref</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.SymbolRef
	 * @generated
	 */
	EClass getSymbolRef();

	/**
	 * Returns the meta object for the reference '{@link org.tetrabox.minijava.model.miniJava.SymbolRef#getSymbol <em>Symbol</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the reference '<em>Symbol</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.SymbolRef#getSymbol()
	 * @see #getSymbolRef()
	 * @generated
	 */
	EReference getSymbolRef_Symbol();

	/**
	 * Returns the meta object for enum '{@link org.tetrabox.minijava.model.miniJava.AccessLevel <em>Access Level</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for enum '<em>Access Level</em>'.
	 * @see org.tetrabox.minijava.model.miniJava.AccessLevel
	 * @generated
	 */
	EEnum getAccessLevel();

	/**
	 * Returns the factory that creates the instances of the model.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the factory that creates the instances of the model.
	 * @generated
	 */
	MiniJavaFactory getMiniJavaFactory();

	/**
	 * <!-- begin-user-doc -->
	 * Defines literals for the meta objects that represent
	 * <ul>
	 *   <li>each class,</li>
	 *   <li>each feature of each class,</li>
	 *   <li>each operation of each class,</li>
	 *   <li>each enum,</li>
	 *   <li>and each data type</li>
	 * </ul>
	 * <!-- end-user-doc -->
	 * @generated
	 */
	interface Literals {
		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ProgramImpl <em>Program</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ProgramImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getProgram()
		 * @generated
		 */
		EClass PROGRAM = eINSTANCE.getProgram();

		/**
		 * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute PROGRAM__NAME = eINSTANCE.getProgram_Name();

		/**
		 * The meta object literal for the '<em><b>Imports</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference PROGRAM__IMPORTS = eINSTANCE.getProgram_Imports();

		/**
		 * The meta object literal for the '<em><b>Classes</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference PROGRAM__CLASSES = eINSTANCE.getProgram_Classes();

		/**
		 * The meta object literal for the '<em><b>State</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference PROGRAM__STATE = eINSTANCE.getProgram_State();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ImportImpl <em>Import</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ImportImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getImport()
		 * @generated
		 */
		EClass IMPORT = eINSTANCE.getImport();

		/**
		 * The meta object literal for the '<em><b>Imported Namespace</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute IMPORT__IMPORTED_NAMESPACE = eINSTANCE.getImport_ImportedNamespace();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.TypeDeclarationImpl <em>Type Declaration</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.TypeDeclarationImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getTypeDeclaration()
		 * @generated
		 */
		EClass TYPE_DECLARATION = eINSTANCE.getTypeDeclaration();

		/**
		 * The meta object literal for the '<em><b>Access Level</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute TYPE_DECLARATION__ACCESS_LEVEL = eINSTANCE.getTypeDeclaration_AccessLevel();

		/**
		 * The meta object literal for the '<em><b>Implements</b></em>' reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference TYPE_DECLARATION__IMPLEMENTS = eINSTANCE.getTypeDeclaration_Implements();

		/**
		 * The meta object literal for the '<em><b>Members</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference TYPE_DECLARATION__MEMBERS = eINSTANCE.getTypeDeclaration_Members();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ClassImpl <em>Class</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ClassImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getClass_()
		 * @generated
		 */
		EClass CLASS = eINSTANCE.getClass_();

		/**
		 * The meta object literal for the '<em><b>Abstract</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute CLASS__ABSTRACT = eINSTANCE.getClass_Abstract();

		/**
		 * The meta object literal for the '<em><b>Super Class</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CLASS__SUPER_CLASS = eINSTANCE.getClass_SuperClass();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.InterfaceImpl <em>Interface</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.InterfaceImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getInterface()
		 * @generated
		 */
		EClass INTERFACE = eINSTANCE.getInterface();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.MemberImpl <em>Member</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.MemberImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getMember()
		 * @generated
		 */
		EClass MEMBER = eINSTANCE.getMember();

		/**
		 * The meta object literal for the '<em><b>Access</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute MEMBER__ACCESS = eINSTANCE.getMember_Access();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.MethodImpl <em>Method</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.MethodImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getMethod()
		 * @generated
		 */
		EClass METHOD = eINSTANCE.getMethod();

		/**
		 * The meta object literal for the '<em><b>Abstract</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute METHOD__ABSTRACT = eINSTANCE.getMethod_Abstract();

		/**
		 * The meta object literal for the '<em><b>Static</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute METHOD__STATIC = eINSTANCE.getMethod_Static();

		/**
		 * The meta object literal for the '<em><b>Params</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference METHOD__PARAMS = eINSTANCE.getMethod_Params();

		/**
		 * The meta object literal for the '<em><b>Body</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference METHOD__BODY = eINSTANCE.getMethod_Body();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ParameterImpl <em>Parameter</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ParameterImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getParameter()
		 * @generated
		 */
		EClass PARAMETER = eINSTANCE.getParameter();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.FieldImpl <em>Field</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.FieldImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getField()
		 * @generated
		 */
		EClass FIELD = eINSTANCE.getField();

		/**
		 * The meta object literal for the '<em><b>Default Value</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FIELD__DEFAULT_VALUE = eINSTANCE.getField_DefaultValue();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.BlockImpl <em>Block</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.BlockImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getBlock()
		 * @generated
		 */
		EClass BLOCK = eINSTANCE.getBlock();

		/**
		 * The meta object literal for the '<em><b>Statements</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference BLOCK__STATEMENTS = eINSTANCE.getBlock_Statements();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.StatementImpl <em>Statement</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.StatementImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getStatement()
		 * @generated
		 */
		EClass STATEMENT = eINSTANCE.getStatement();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.PrintStatementImpl <em>Print Statement</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.PrintStatementImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getPrintStatement()
		 * @generated
		 */
		EClass PRINT_STATEMENT = eINSTANCE.getPrintStatement();

		/**
		 * The meta object literal for the '<em><b>Expression</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference PRINT_STATEMENT__EXPRESSION = eINSTANCE.getPrintStatement_Expression();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ReturnImpl <em>Return</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ReturnImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getReturn()
		 * @generated
		 */
		EClass RETURN = eINSTANCE.getReturn();

		/**
		 * The meta object literal for the '<em><b>Expression</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference RETURN__EXPRESSION = eINSTANCE.getReturn_Expression();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.IfStatementImpl <em>If Statement</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.IfStatementImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getIfStatement()
		 * @generated
		 */
		EClass IF_STATEMENT = eINSTANCE.getIfStatement();

		/**
		 * The meta object literal for the '<em><b>Expression</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference IF_STATEMENT__EXPRESSION = eINSTANCE.getIfStatement_Expression();

		/**
		 * The meta object literal for the '<em><b>Then Block</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference IF_STATEMENT__THEN_BLOCK = eINSTANCE.getIfStatement_ThenBlock();

		/**
		 * The meta object literal for the '<em><b>Else Block</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference IF_STATEMENT__ELSE_BLOCK = eINSTANCE.getIfStatement_ElseBlock();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.WhileStatementImpl <em>While Statement</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.WhileStatementImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getWhileStatement()
		 * @generated
		 */
		EClass WHILE_STATEMENT = eINSTANCE.getWhileStatement();

		/**
		 * The meta object literal for the '<em><b>Condition</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference WHILE_STATEMENT__CONDITION = eINSTANCE.getWhileStatement_Condition();

		/**
		 * The meta object literal for the '<em><b>Block</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference WHILE_STATEMENT__BLOCK = eINSTANCE.getWhileStatement_Block();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ForStatementImpl <em>For Statement</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ForStatementImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getForStatement()
		 * @generated
		 */
		EClass FOR_STATEMENT = eINSTANCE.getForStatement();

		/**
		 * The meta object literal for the '<em><b>Declaration</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FOR_STATEMENT__DECLARATION = eINSTANCE.getForStatement_Declaration();

		/**
		 * The meta object literal for the '<em><b>Condition</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FOR_STATEMENT__CONDITION = eINSTANCE.getForStatement_Condition();

		/**
		 * The meta object literal for the '<em><b>Progression</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FOR_STATEMENT__PROGRESSION = eINSTANCE.getForStatement_Progression();

		/**
		 * The meta object literal for the '<em><b>Block</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FOR_STATEMENT__BLOCK = eINSTANCE.getForStatement_Block();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.TypeRefImpl <em>Type Ref</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.TypeRefImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getTypeRef()
		 * @generated
		 */
		EClass TYPE_REF = eINSTANCE.getTypeRef();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.SingleTypeRefImpl <em>Single Type Ref</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.SingleTypeRefImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSingleTypeRef()
		 * @generated
		 */
		EClass SINGLE_TYPE_REF = eINSTANCE.getSingleTypeRef();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ClassRefImpl <em>Class Ref</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ClassRefImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getClassRef()
		 * @generated
		 */
		EClass CLASS_REF = eINSTANCE.getClassRef();

		/**
		 * The meta object literal for the '<em><b>Referenced Class</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference CLASS_REF__REFERENCED_CLASS = eINSTANCE.getClassRef_ReferencedClass();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.NamedElementImpl <em>Named Element</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.NamedElementImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNamedElement()
		 * @generated
		 */
		EClass NAMED_ELEMENT = eINSTANCE.getNamedElement();

		/**
		 * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute NAMED_ELEMENT__NAME = eINSTANCE.getNamedElement_Name();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.TypedDeclarationImpl <em>Typed Declaration</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.TypedDeclarationImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getTypedDeclaration()
		 * @generated
		 */
		EClass TYPED_DECLARATION = eINSTANCE.getTypedDeclaration();

		/**
		 * The meta object literal for the '<em><b>Type Ref</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference TYPED_DECLARATION__TYPE_REF = eINSTANCE.getTypedDeclaration_TypeRef();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.SymbolImpl <em>Symbol</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.SymbolImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSymbol()
		 * @generated
		 */
		EClass SYMBOL = eINSTANCE.getSymbol();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.VariableDeclarationImpl <em>Variable Declaration</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.VariableDeclarationImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getVariableDeclaration()
		 * @generated
		 */
		EClass VARIABLE_DECLARATION = eINSTANCE.getVariableDeclaration();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.AssignmentImpl <em>Assignment</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.AssignmentImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getAssignment()
		 * @generated
		 */
		EClass ASSIGNMENT = eINSTANCE.getAssignment();

		/**
		 * The meta object literal for the '<em><b>Assignee</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ASSIGNMENT__ASSIGNEE = eINSTANCE.getAssignment_Assignee();

		/**
		 * The meta object literal for the '<em><b>Value</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ASSIGNMENT__VALUE = eINSTANCE.getAssignment_Value();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.AssigneeImpl <em>Assignee</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.AssigneeImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getAssignee()
		 * @generated
		 */
		EClass ASSIGNEE = eINSTANCE.getAssignee();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ExpressionImpl <em>Expression</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ExpressionImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getExpression()
		 * @generated
		 */
		EClass EXPRESSION = eINSTANCE.getExpression();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ArrayTypeRefImpl <em>Array Type Ref</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ArrayTypeRefImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getArrayTypeRef()
		 * @generated
		 */
		EClass ARRAY_TYPE_REF = eINSTANCE.getArrayTypeRef();

		/**
		 * The meta object literal for the '<em><b>Type Ref</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ARRAY_TYPE_REF__TYPE_REF = eINSTANCE.getArrayTypeRef_TypeRef();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.IntegerTypeRefImpl <em>Integer Type Ref</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.IntegerTypeRefImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getIntegerTypeRef()
		 * @generated
		 */
		EClass INTEGER_TYPE_REF = eINSTANCE.getIntegerTypeRef();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.BooleanTypeRefImpl <em>Boolean Type Ref</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.BooleanTypeRefImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getBooleanTypeRef()
		 * @generated
		 */
		EClass BOOLEAN_TYPE_REF = eINSTANCE.getBooleanTypeRef();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.StringTypeRefImpl <em>String Type Ref</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.StringTypeRefImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getStringTypeRef()
		 * @generated
		 */
		EClass STRING_TYPE_REF = eINSTANCE.getStringTypeRef();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.VoidTypeRefImpl <em>Void Type Ref</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.VoidTypeRefImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getVoidTypeRef()
		 * @generated
		 */
		EClass VOID_TYPE_REF = eINSTANCE.getVoidTypeRef();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.OrImpl <em>Or</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.OrImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getOr()
		 * @generated
		 */
		EClass OR = eINSTANCE.getOr();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference OR__LEFT = eINSTANCE.getOr_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference OR__RIGHT = eINSTANCE.getOr_Right();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.AndImpl <em>And</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.AndImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getAnd()
		 * @generated
		 */
		EClass AND = eINSTANCE.getAnd();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference AND__LEFT = eINSTANCE.getAnd_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference AND__RIGHT = eINSTANCE.getAnd_Right();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.EqualityImpl <em>Equality</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.EqualityImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getEquality()
		 * @generated
		 */
		EClass EQUALITY = eINSTANCE.getEquality();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference EQUALITY__LEFT = eINSTANCE.getEquality_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference EQUALITY__RIGHT = eINSTANCE.getEquality_Right();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.InequalityImpl <em>Inequality</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.InequalityImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getInequality()
		 * @generated
		 */
		EClass INEQUALITY = eINSTANCE.getInequality();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference INEQUALITY__LEFT = eINSTANCE.getInequality_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference INEQUALITY__RIGHT = eINSTANCE.getInequality_Right();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.SuperiorOrEqualImpl <em>Superior Or Equal</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.SuperiorOrEqualImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSuperiorOrEqual()
		 * @generated
		 */
		EClass SUPERIOR_OR_EQUAL = eINSTANCE.getSuperiorOrEqual();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference SUPERIOR_OR_EQUAL__LEFT = eINSTANCE.getSuperiorOrEqual_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference SUPERIOR_OR_EQUAL__RIGHT = eINSTANCE.getSuperiorOrEqual_Right();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.InferiorOrEqualImpl <em>Inferior Or Equal</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.InferiorOrEqualImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getInferiorOrEqual()
		 * @generated
		 */
		EClass INFERIOR_OR_EQUAL = eINSTANCE.getInferiorOrEqual();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference INFERIOR_OR_EQUAL__LEFT = eINSTANCE.getInferiorOrEqual_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference INFERIOR_OR_EQUAL__RIGHT = eINSTANCE.getInferiorOrEqual_Right();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.SuperiorImpl <em>Superior</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.SuperiorImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSuperior()
		 * @generated
		 */
		EClass SUPERIOR = eINSTANCE.getSuperior();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference SUPERIOR__LEFT = eINSTANCE.getSuperior_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference SUPERIOR__RIGHT = eINSTANCE.getSuperior_Right();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.InferiorImpl <em>Inferior</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.InferiorImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getInferior()
		 * @generated
		 */
		EClass INFERIOR = eINSTANCE.getInferior();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference INFERIOR__LEFT = eINSTANCE.getInferior_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference INFERIOR__RIGHT = eINSTANCE.getInferior_Right();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.PlusImpl <em>Plus</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.PlusImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getPlus()
		 * @generated
		 */
		EClass PLUS = eINSTANCE.getPlus();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference PLUS__LEFT = eINSTANCE.getPlus_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference PLUS__RIGHT = eINSTANCE.getPlus_Right();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.MinusImpl <em>Minus</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.MinusImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getMinus()
		 * @generated
		 */
		EClass MINUS = eINSTANCE.getMinus();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference MINUS__LEFT = eINSTANCE.getMinus_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference MINUS__RIGHT = eINSTANCE.getMinus_Right();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.MultiplicationImpl <em>Multiplication</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.MultiplicationImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getMultiplication()
		 * @generated
		 */
		EClass MULTIPLICATION = eINSTANCE.getMultiplication();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference MULTIPLICATION__LEFT = eINSTANCE.getMultiplication_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference MULTIPLICATION__RIGHT = eINSTANCE.getMultiplication_Right();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.DivisionImpl <em>Division</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.DivisionImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getDivision()
		 * @generated
		 */
		EClass DIVISION = eINSTANCE.getDivision();

		/**
		 * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference DIVISION__LEFT = eINSTANCE.getDivision_Left();

		/**
		 * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference DIVISION__RIGHT = eINSTANCE.getDivision_Right();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ArrayAccessImpl <em>Array Access</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ArrayAccessImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getArrayAccess()
		 * @generated
		 */
		EClass ARRAY_ACCESS = eINSTANCE.getArrayAccess();

		/**
		 * The meta object literal for the '<em><b>Object</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ARRAY_ACCESS__OBJECT = eINSTANCE.getArrayAccess_Object();

		/**
		 * The meta object literal for the '<em><b>Index</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ARRAY_ACCESS__INDEX = eINSTANCE.getArrayAccess_Index();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ArrayLengthImpl <em>Array Length</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ArrayLengthImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getArrayLength()
		 * @generated
		 */
		EClass ARRAY_LENGTH = eINSTANCE.getArrayLength();

		/**
		 * The meta object literal for the '<em><b>Array</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference ARRAY_LENGTH__ARRAY = eINSTANCE.getArrayLength_Array();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.NotImpl <em>Not</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.NotImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNot()
		 * @generated
		 */
		EClass NOT = eINSTANCE.getNot();

		/**
		 * The meta object literal for the '<em><b>Expression</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference NOT__EXPRESSION = eINSTANCE.getNot_Expression();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.NegImpl <em>Neg</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.NegImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNeg()
		 * @generated
		 */
		EClass NEG = eINSTANCE.getNeg();

		/**
		 * The meta object literal for the '<em><b>Expression</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference NEG__EXPRESSION = eINSTANCE.getNeg_Expression();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.FieldAccessImpl <em>Field Access</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.FieldAccessImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getFieldAccess()
		 * @generated
		 */
		EClass FIELD_ACCESS = eINSTANCE.getFieldAccess();

		/**
		 * The meta object literal for the '<em><b>Receiver</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FIELD_ACCESS__RECEIVER = eINSTANCE.getFieldAccess_Receiver();

		/**
		 * The meta object literal for the '<em><b>Field</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference FIELD_ACCESS__FIELD = eINSTANCE.getFieldAccess_Field();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.MethodCallImpl <em>Method Call</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.MethodCallImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getMethodCall()
		 * @generated
		 */
		EClass METHOD_CALL = eINSTANCE.getMethodCall();

		/**
		 * The meta object literal for the '<em><b>Receiver</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference METHOD_CALL__RECEIVER = eINSTANCE.getMethodCall_Receiver();

		/**
		 * The meta object literal for the '<em><b>Method</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference METHOD_CALL__METHOD = eINSTANCE.getMethodCall_Method();

		/**
		 * The meta object literal for the '<em><b>Args</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference METHOD_CALL__ARGS = eINSTANCE.getMethodCall_Args();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.StringConstantImpl <em>String Constant</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.StringConstantImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getStringConstant()
		 * @generated
		 */
		EClass STRING_CONSTANT = eINSTANCE.getStringConstant();

		/**
		 * The meta object literal for the '<em><b>Value</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute STRING_CONSTANT__VALUE = eINSTANCE.getStringConstant_Value();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.IntConstantImpl <em>Int Constant</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.IntConstantImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getIntConstant()
		 * @generated
		 */
		EClass INT_CONSTANT = eINSTANCE.getIntConstant();

		/**
		 * The meta object literal for the '<em><b>Value</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute INT_CONSTANT__VALUE = eINSTANCE.getIntConstant_Value();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.BoolConstantImpl <em>Bool Constant</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.BoolConstantImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getBoolConstant()
		 * @generated
		 */
		EClass BOOL_CONSTANT = eINSTANCE.getBoolConstant();

		/**
		 * The meta object literal for the '<em><b>Value</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute BOOL_CONSTANT__VALUE = eINSTANCE.getBoolConstant_Value();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.ThisImpl <em>This</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.ThisImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getThis()
		 * @generated
		 */
		EClass THIS = eINSTANCE.getThis();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.SuperImpl <em>Super</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.SuperImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSuper()
		 * @generated
		 */
		EClass SUPER = eINSTANCE.getSuper();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.NullImpl <em>Null</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.NullImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNull()
		 * @generated
		 */
		EClass NULL = eINSTANCE.getNull();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.NewObjectImpl <em>New Object</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.NewObjectImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNewObject()
		 * @generated
		 */
		EClass NEW_OBJECT = eINSTANCE.getNewObject();

		/**
		 * The meta object literal for the '<em><b>Type</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference NEW_OBJECT__TYPE = eINSTANCE.getNewObject_Type();

		/**
		 * The meta object literal for the '<em><b>Args</b></em>' containment reference list feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference NEW_OBJECT__ARGS = eINSTANCE.getNewObject_Args();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.NewArrayImpl <em>New Array</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.NewArrayImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getNewArray()
		 * @generated
		 */
		EClass NEW_ARRAY = eINSTANCE.getNewArray();

		/**
		 * The meta object literal for the '<em><b>Type</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference NEW_ARRAY__TYPE = eINSTANCE.getNewArray_Type();

		/**
		 * The meta object literal for the '<em><b>Size</b></em>' containment reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference NEW_ARRAY__SIZE = eINSTANCE.getNewArray_Size();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.impl.SymbolRefImpl <em>Symbol Ref</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.impl.SymbolRefImpl
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getSymbolRef()
		 * @generated
		 */
		EClass SYMBOL_REF = eINSTANCE.getSymbolRef();

		/**
		 * The meta object literal for the '<em><b>Symbol</b></em>' reference feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EReference SYMBOL_REF__SYMBOL = eINSTANCE.getSymbolRef_Symbol();

		/**
		 * The meta object literal for the '{@link org.tetrabox.minijava.model.miniJava.AccessLevel <em>Access Level</em>}' enum.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see org.tetrabox.minijava.model.miniJava.AccessLevel
		 * @see org.tetrabox.minijava.model.miniJava.impl.MiniJavaPackageImpl#getAccessLevel()
		 * @generated
		 */
		EEnum ACCESS_LEVEL = eINSTANCE.getAccessLevel();

	}

} //MiniJavaPackage
