package org.tetrabox.minijava.xtext.ide.contentassist.antlr.internal;

import java.io.InputStream;
import org.eclipse.xtext.*;
import org.eclipse.xtext.parser.*;
import org.eclipse.xtext.parser.impl.*;
import org.eclipse.emf.ecore.util.EcoreUtil;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.parser.antlr.XtextTokenStream;
import org.eclipse.xtext.parser.antlr.XtextTokenStream.HiddenTokens;
import org.eclipse.xtext.ide.editor.contentassist.antlr.internal.AbstractInternalContentAssistParser;
import org.eclipse.xtext.ide.editor.contentassist.antlr.internal.DFA;
import org.tetrabox.minijava.xtext.services.MiniJavaGrammarAccess;



import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;
@SuppressWarnings("all")
public class InternalMiniJavaParser extends AbstractInternalContentAssistParser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "RULE_ID", "RULE_STRING", "RULE_INT", "RULE_ML_COMMENT", "RULE_SL_COMMENT", "RULE_WS", "RULE_ANY_OTHER", "';'", "'true'", "'false'", "'private'", "'protected'", "'public'", "'package'", "'import'", "'.'", "'.*'", "'class'", "'{'", "'}'", "'extends'", "'implements'", "','", "'interface'", "'('", "')'", "'='", "'System'", "'out'", "'println'", "'return'", "'if'", "'else'", "'while'", "'for'", "'['", "']'", "'int'", "'boolean'", "'String'", "'void'", "'||'", "'&&'", "'=='", "'!='", "'>='", "'<='", "'>'", "'<'", "'+'", "'-'", "'*'", "'/'", "'length'", "'!'", "'this'", "'super'", "'null'", "'new'", "'abstract'", "'static'"
    };
    public static final int T__50=50;
    public static final int T__19=19;
    public static final int T__15=15;
    public static final int T__59=59;
    public static final int T__16=16;
    public static final int T__17=17;
    public static final int T__18=18;
    public static final int T__11=11;
    public static final int T__55=55;
    public static final int T__12=12;
    public static final int T__56=56;
    public static final int T__13=13;
    public static final int T__57=57;
    public static final int T__14=14;
    public static final int T__58=58;
    public static final int T__51=51;
    public static final int T__52=52;
    public static final int T__53=53;
    public static final int T__54=54;
    public static final int T__60=60;
    public static final int T__61=61;
    public static final int RULE_ID=4;
    public static final int T__26=26;
    public static final int T__27=27;
    public static final int T__28=28;
    public static final int RULE_INT=6;
    public static final int T__29=29;
    public static final int T__22=22;
    public static final int RULE_ML_COMMENT=7;
    public static final int T__23=23;
    public static final int T__24=24;
    public static final int T__25=25;
    public static final int T__62=62;
    public static final int T__63=63;
    public static final int T__20=20;
    public static final int T__64=64;
    public static final int T__21=21;
    public static final int RULE_STRING=5;
    public static final int RULE_SL_COMMENT=8;
    public static final int T__37=37;
    public static final int T__38=38;
    public static final int T__39=39;
    public static final int T__33=33;
    public static final int T__34=34;
    public static final int T__35=35;
    public static final int T__36=36;
    public static final int EOF=-1;
    public static final int T__30=30;
    public static final int T__31=31;
    public static final int T__32=32;
    public static final int RULE_WS=9;
    public static final int RULE_ANY_OTHER=10;
    public static final int T__48=48;
    public static final int T__49=49;
    public static final int T__44=44;
    public static final int T__45=45;
    public static final int T__46=46;
    public static final int T__47=47;
    public static final int T__40=40;
    public static final int T__41=41;
    public static final int T__42=42;
    public static final int T__43=43;

    // delegates
    // delegators


        public InternalMiniJavaParser(TokenStream input) {
            this(input, new RecognizerSharedState());
        }
        public InternalMiniJavaParser(TokenStream input, RecognizerSharedState state) {
            super(input, state);
             
        }
        

    public String[] getTokenNames() { return InternalMiniJavaParser.tokenNames; }
    public String getGrammarFileName() { return "InternalMiniJava.g"; }


    	private MiniJavaGrammarAccess grammarAccess;

    	public void setGrammarAccess(MiniJavaGrammarAccess grammarAccess) {
    		this.grammarAccess = grammarAccess;
    	}

    	@Override
    	protected Grammar getGrammar() {
    		return grammarAccess.getGrammar();
    	}

    	@Override
    	protected String getValueForTokenName(String tokenName) {
    		return tokenName;
    	}



    // $ANTLR start "entryRuleProgram"
    // InternalMiniJava.g:54:1: entryRuleProgram : ruleProgram EOF ;
    public final void entryRuleProgram() throws RecognitionException {
        try {
            // InternalMiniJava.g:55:1: ( ruleProgram EOF )
            // InternalMiniJava.g:56:1: ruleProgram EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getProgramRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleProgram();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getProgramRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleProgram"


    // $ANTLR start "ruleProgram"
    // InternalMiniJava.g:63:1: ruleProgram : ( ( rule__Program__Group__0 ) ) ;
    public final void ruleProgram() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:67:2: ( ( ( rule__Program__Group__0 ) ) )
            // InternalMiniJava.g:68:2: ( ( rule__Program__Group__0 ) )
            {
            // InternalMiniJava.g:68:2: ( ( rule__Program__Group__0 ) )
            // InternalMiniJava.g:69:3: ( rule__Program__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getProgramAccess().getGroup()); 
            }
            // InternalMiniJava.g:70:3: ( rule__Program__Group__0 )
            // InternalMiniJava.g:70:4: rule__Program__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__Program__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getProgramAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleProgram"


    // $ANTLR start "entryRuleImport"
    // InternalMiniJava.g:79:1: entryRuleImport : ruleImport EOF ;
    public final void entryRuleImport() throws RecognitionException {
        try {
            // InternalMiniJava.g:80:1: ( ruleImport EOF )
            // InternalMiniJava.g:81:1: ruleImport EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getImportRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleImport();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getImportRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleImport"


    // $ANTLR start "ruleImport"
    // InternalMiniJava.g:88:1: ruleImport : ( ( rule__Import__Group__0 ) ) ;
    public final void ruleImport() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:92:2: ( ( ( rule__Import__Group__0 ) ) )
            // InternalMiniJava.g:93:2: ( ( rule__Import__Group__0 ) )
            {
            // InternalMiniJava.g:93:2: ( ( rule__Import__Group__0 ) )
            // InternalMiniJava.g:94:3: ( rule__Import__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getImportAccess().getGroup()); 
            }
            // InternalMiniJava.g:95:3: ( rule__Import__Group__0 )
            // InternalMiniJava.g:95:4: rule__Import__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__Import__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getImportAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleImport"


    // $ANTLR start "entryRuleQualifiedName"
    // InternalMiniJava.g:104:1: entryRuleQualifiedName : ruleQualifiedName EOF ;
    public final void entryRuleQualifiedName() throws RecognitionException {
        try {
            // InternalMiniJava.g:105:1: ( ruleQualifiedName EOF )
            // InternalMiniJava.g:106:1: ruleQualifiedName EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getQualifiedNameRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleQualifiedName();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getQualifiedNameRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleQualifiedName"


    // $ANTLR start "ruleQualifiedName"
    // InternalMiniJava.g:113:1: ruleQualifiedName : ( ( rule__QualifiedName__Group__0 ) ) ;
    public final void ruleQualifiedName() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:117:2: ( ( ( rule__QualifiedName__Group__0 ) ) )
            // InternalMiniJava.g:118:2: ( ( rule__QualifiedName__Group__0 ) )
            {
            // InternalMiniJava.g:118:2: ( ( rule__QualifiedName__Group__0 ) )
            // InternalMiniJava.g:119:3: ( rule__QualifiedName__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getQualifiedNameAccess().getGroup()); 
            }
            // InternalMiniJava.g:120:3: ( rule__QualifiedName__Group__0 )
            // InternalMiniJava.g:120:4: rule__QualifiedName__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__QualifiedName__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getQualifiedNameAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleQualifiedName"


    // $ANTLR start "entryRuleQualifiedNameWithWildcard"
    // InternalMiniJava.g:129:1: entryRuleQualifiedNameWithWildcard : ruleQualifiedNameWithWildcard EOF ;
    public final void entryRuleQualifiedNameWithWildcard() throws RecognitionException {
        try {
            // InternalMiniJava.g:130:1: ( ruleQualifiedNameWithWildcard EOF )
            // InternalMiniJava.g:131:1: ruleQualifiedNameWithWildcard EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getQualifiedNameWithWildcardRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleQualifiedNameWithWildcard();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getQualifiedNameWithWildcardRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleQualifiedNameWithWildcard"


    // $ANTLR start "ruleQualifiedNameWithWildcard"
    // InternalMiniJava.g:138:1: ruleQualifiedNameWithWildcard : ( ( rule__QualifiedNameWithWildcard__Group__0 ) ) ;
    public final void ruleQualifiedNameWithWildcard() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:142:2: ( ( ( rule__QualifiedNameWithWildcard__Group__0 ) ) )
            // InternalMiniJava.g:143:2: ( ( rule__QualifiedNameWithWildcard__Group__0 ) )
            {
            // InternalMiniJava.g:143:2: ( ( rule__QualifiedNameWithWildcard__Group__0 ) )
            // InternalMiniJava.g:144:3: ( rule__QualifiedNameWithWildcard__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getQualifiedNameWithWildcardAccess().getGroup()); 
            }
            // InternalMiniJava.g:145:3: ( rule__QualifiedNameWithWildcard__Group__0 )
            // InternalMiniJava.g:145:4: rule__QualifiedNameWithWildcard__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__QualifiedNameWithWildcard__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getQualifiedNameWithWildcardAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleQualifiedNameWithWildcard"


    // $ANTLR start "entryRuleTypeDeclaration"
    // InternalMiniJava.g:154:1: entryRuleTypeDeclaration : ruleTypeDeclaration EOF ;
    public final void entryRuleTypeDeclaration() throws RecognitionException {
        try {
            // InternalMiniJava.g:155:1: ( ruleTypeDeclaration EOF )
            // InternalMiniJava.g:156:1: ruleTypeDeclaration EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTypeDeclarationRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleTypeDeclaration();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTypeDeclarationRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleTypeDeclaration"


    // $ANTLR start "ruleTypeDeclaration"
    // InternalMiniJava.g:163:1: ruleTypeDeclaration : ( ( rule__TypeDeclaration__Alternatives ) ) ;
    public final void ruleTypeDeclaration() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:167:2: ( ( ( rule__TypeDeclaration__Alternatives ) ) )
            // InternalMiniJava.g:168:2: ( ( rule__TypeDeclaration__Alternatives ) )
            {
            // InternalMiniJava.g:168:2: ( ( rule__TypeDeclaration__Alternatives ) )
            // InternalMiniJava.g:169:3: ( rule__TypeDeclaration__Alternatives )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTypeDeclarationAccess().getAlternatives()); 
            }
            // InternalMiniJava.g:170:3: ( rule__TypeDeclaration__Alternatives )
            // InternalMiniJava.g:170:4: rule__TypeDeclaration__Alternatives
            {
            pushFollow(FOLLOW_2);
            rule__TypeDeclaration__Alternatives();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTypeDeclarationAccess().getAlternatives()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleTypeDeclaration"


    // $ANTLR start "entryRuleClass"
    // InternalMiniJava.g:179:1: entryRuleClass : ruleClass EOF ;
    public final void entryRuleClass() throws RecognitionException {
        try {
            // InternalMiniJava.g:180:1: ( ruleClass EOF )
            // InternalMiniJava.g:181:1: ruleClass EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleClass();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleClass"


    // $ANTLR start "ruleClass"
    // InternalMiniJava.g:188:1: ruleClass : ( ( rule__Class__Group__0 ) ) ;
    public final void ruleClass() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:192:2: ( ( ( rule__Class__Group__0 ) ) )
            // InternalMiniJava.g:193:2: ( ( rule__Class__Group__0 ) )
            {
            // InternalMiniJava.g:193:2: ( ( rule__Class__Group__0 ) )
            // InternalMiniJava.g:194:3: ( rule__Class__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getGroup()); 
            }
            // InternalMiniJava.g:195:3: ( rule__Class__Group__0 )
            // InternalMiniJava.g:195:4: rule__Class__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__Class__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleClass"


    // $ANTLR start "entryRuleInterface"
    // InternalMiniJava.g:204:1: entryRuleInterface : ruleInterface EOF ;
    public final void entryRuleInterface() throws RecognitionException {
        try {
            // InternalMiniJava.g:205:1: ( ruleInterface EOF )
            // InternalMiniJava.g:206:1: ruleInterface EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getInterfaceRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleInterface();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getInterfaceRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleInterface"


    // $ANTLR start "ruleInterface"
    // InternalMiniJava.g:213:1: ruleInterface : ( ( rule__Interface__Group__0 ) ) ;
    public final void ruleInterface() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:217:2: ( ( ( rule__Interface__Group__0 ) ) )
            // InternalMiniJava.g:218:2: ( ( rule__Interface__Group__0 ) )
            {
            // InternalMiniJava.g:218:2: ( ( rule__Interface__Group__0 ) )
            // InternalMiniJava.g:219:3: ( rule__Interface__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getInterfaceAccess().getGroup()); 
            }
            // InternalMiniJava.g:220:3: ( rule__Interface__Group__0 )
            // InternalMiniJava.g:220:4: rule__Interface__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__Interface__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getInterfaceAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleInterface"


    // $ANTLR start "entryRuleMember"
    // InternalMiniJava.g:229:1: entryRuleMember : ruleMember EOF ;
    public final void entryRuleMember() throws RecognitionException {
        try {
            // InternalMiniJava.g:230:1: ( ruleMember EOF )
            // InternalMiniJava.g:231:1: ruleMember EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMemberRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleMember();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getMemberRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleMember"


    // $ANTLR start "ruleMember"
    // InternalMiniJava.g:238:1: ruleMember : ( ( rule__Member__Alternatives ) ) ;
    public final void ruleMember() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:242:2: ( ( ( rule__Member__Alternatives ) ) )
            // InternalMiniJava.g:243:2: ( ( rule__Member__Alternatives ) )
            {
            // InternalMiniJava.g:243:2: ( ( rule__Member__Alternatives ) )
            // InternalMiniJava.g:244:3: ( rule__Member__Alternatives )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMemberAccess().getAlternatives()); 
            }
            // InternalMiniJava.g:245:3: ( rule__Member__Alternatives )
            // InternalMiniJava.g:245:4: rule__Member__Alternatives
            {
            pushFollow(FOLLOW_2);
            rule__Member__Alternatives();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getMemberAccess().getAlternatives()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleMember"


    // $ANTLR start "entryRuleMethod"
    // InternalMiniJava.g:254:1: entryRuleMethod : ruleMethod EOF ;
    public final void entryRuleMethod() throws RecognitionException {
        try {
            // InternalMiniJava.g:255:1: ( ruleMethod EOF )
            // InternalMiniJava.g:256:1: ruleMethod EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleMethod();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleMethod"


    // $ANTLR start "ruleMethod"
    // InternalMiniJava.g:263:1: ruleMethod : ( ( rule__Method__Group__0 ) ) ;
    public final void ruleMethod() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:267:2: ( ( ( rule__Method__Group__0 ) ) )
            // InternalMiniJava.g:268:2: ( ( rule__Method__Group__0 ) )
            {
            // InternalMiniJava.g:268:2: ( ( rule__Method__Group__0 ) )
            // InternalMiniJava.g:269:3: ( rule__Method__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getGroup()); 
            }
            // InternalMiniJava.g:270:3: ( rule__Method__Group__0 )
            // InternalMiniJava.g:270:4: rule__Method__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__Method__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleMethod"


    // $ANTLR start "entryRuleParameter"
    // InternalMiniJava.g:279:1: entryRuleParameter : ruleParameter EOF ;
    public final void entryRuleParameter() throws RecognitionException {
        try {
            // InternalMiniJava.g:280:1: ( ruleParameter EOF )
            // InternalMiniJava.g:281:1: ruleParameter EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getParameterRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleParameter();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getParameterRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleParameter"


    // $ANTLR start "ruleParameter"
    // InternalMiniJava.g:288:1: ruleParameter : ( ( rule__Parameter__Group__0 ) ) ;
    public final void ruleParameter() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:292:2: ( ( ( rule__Parameter__Group__0 ) ) )
            // InternalMiniJava.g:293:2: ( ( rule__Parameter__Group__0 ) )
            {
            // InternalMiniJava.g:293:2: ( ( rule__Parameter__Group__0 ) )
            // InternalMiniJava.g:294:3: ( rule__Parameter__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getParameterAccess().getGroup()); 
            }
            // InternalMiniJava.g:295:3: ( rule__Parameter__Group__0 )
            // InternalMiniJava.g:295:4: rule__Parameter__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__Parameter__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getParameterAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleParameter"


    // $ANTLR start "entryRuleField"
    // InternalMiniJava.g:304:1: entryRuleField : ruleField EOF ;
    public final void entryRuleField() throws RecognitionException {
        try {
            // InternalMiniJava.g:305:1: ( ruleField EOF )
            // InternalMiniJava.g:306:1: ruleField EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getFieldRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleField();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getFieldRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleField"


    // $ANTLR start "ruleField"
    // InternalMiniJava.g:313:1: ruleField : ( ( rule__Field__Group__0 ) ) ;
    public final void ruleField() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:317:2: ( ( ( rule__Field__Group__0 ) ) )
            // InternalMiniJava.g:318:2: ( ( rule__Field__Group__0 ) )
            {
            // InternalMiniJava.g:318:2: ( ( rule__Field__Group__0 ) )
            // InternalMiniJava.g:319:3: ( rule__Field__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getFieldAccess().getGroup()); 
            }
            // InternalMiniJava.g:320:3: ( rule__Field__Group__0 )
            // InternalMiniJava.g:320:4: rule__Field__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__Field__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getFieldAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleField"


    // $ANTLR start "entryRuleBlock"
    // InternalMiniJava.g:329:1: entryRuleBlock : ruleBlock EOF ;
    public final void entryRuleBlock() throws RecognitionException {
        try {
            // InternalMiniJava.g:330:1: ( ruleBlock EOF )
            // InternalMiniJava.g:331:1: ruleBlock EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getBlockRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleBlock();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getBlockRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleBlock"


    // $ANTLR start "ruleBlock"
    // InternalMiniJava.g:338:1: ruleBlock : ( ( rule__Block__Group__0 ) ) ;
    public final void ruleBlock() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:342:2: ( ( ( rule__Block__Group__0 ) ) )
            // InternalMiniJava.g:343:2: ( ( rule__Block__Group__0 ) )
            {
            // InternalMiniJava.g:343:2: ( ( rule__Block__Group__0 ) )
            // InternalMiniJava.g:344:3: ( rule__Block__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getBlockAccess().getGroup()); 
            }
            // InternalMiniJava.g:345:3: ( rule__Block__Group__0 )
            // InternalMiniJava.g:345:4: rule__Block__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__Block__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getBlockAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleBlock"


    // $ANTLR start "entryRuleStatement"
    // InternalMiniJava.g:354:1: entryRuleStatement : ruleStatement EOF ;
    public final void entryRuleStatement() throws RecognitionException {
        try {
            // InternalMiniJava.g:355:1: ( ruleStatement EOF )
            // InternalMiniJava.g:356:1: ruleStatement EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getStatementRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleStatement();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getStatementRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleStatement"


    // $ANTLR start "ruleStatement"
    // InternalMiniJava.g:363:1: ruleStatement : ( ( rule__Statement__Alternatives ) ) ;
    public final void ruleStatement() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:367:2: ( ( ( rule__Statement__Alternatives ) ) )
            // InternalMiniJava.g:368:2: ( ( rule__Statement__Alternatives ) )
            {
            // InternalMiniJava.g:368:2: ( ( rule__Statement__Alternatives ) )
            // InternalMiniJava.g:369:3: ( rule__Statement__Alternatives )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getStatementAccess().getAlternatives()); 
            }
            // InternalMiniJava.g:370:3: ( rule__Statement__Alternatives )
            // InternalMiniJava.g:370:4: rule__Statement__Alternatives
            {
            pushFollow(FOLLOW_2);
            rule__Statement__Alternatives();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getStatementAccess().getAlternatives()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleStatement"


    // $ANTLR start "entryRulePrintStatement"
    // InternalMiniJava.g:379:1: entryRulePrintStatement : rulePrintStatement EOF ;
    public final void entryRulePrintStatement() throws RecognitionException {
        try {
            // InternalMiniJava.g:380:1: ( rulePrintStatement EOF )
            // InternalMiniJava.g:381:1: rulePrintStatement EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrintStatementRule()); 
            }
            pushFollow(FOLLOW_1);
            rulePrintStatement();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrintStatementRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRulePrintStatement"


    // $ANTLR start "rulePrintStatement"
    // InternalMiniJava.g:388:1: rulePrintStatement : ( ( rule__PrintStatement__Group__0 ) ) ;
    public final void rulePrintStatement() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:392:2: ( ( ( rule__PrintStatement__Group__0 ) ) )
            // InternalMiniJava.g:393:2: ( ( rule__PrintStatement__Group__0 ) )
            {
            // InternalMiniJava.g:393:2: ( ( rule__PrintStatement__Group__0 ) )
            // InternalMiniJava.g:394:3: ( rule__PrintStatement__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrintStatementAccess().getGroup()); 
            }
            // InternalMiniJava.g:395:3: ( rule__PrintStatement__Group__0 )
            // InternalMiniJava.g:395:4: rule__PrintStatement__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__PrintStatement__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrintStatementAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rulePrintStatement"


    // $ANTLR start "entryRuleReturn"
    // InternalMiniJava.g:404:1: entryRuleReturn : ruleReturn EOF ;
    public final void entryRuleReturn() throws RecognitionException {
        try {
            // InternalMiniJava.g:405:1: ( ruleReturn EOF )
            // InternalMiniJava.g:406:1: ruleReturn EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getReturnRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleReturn();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getReturnRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleReturn"


    // $ANTLR start "ruleReturn"
    // InternalMiniJava.g:413:1: ruleReturn : ( ( rule__Return__Group__0 ) ) ;
    public final void ruleReturn() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:417:2: ( ( ( rule__Return__Group__0 ) ) )
            // InternalMiniJava.g:418:2: ( ( rule__Return__Group__0 ) )
            {
            // InternalMiniJava.g:418:2: ( ( rule__Return__Group__0 ) )
            // InternalMiniJava.g:419:3: ( rule__Return__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getReturnAccess().getGroup()); 
            }
            // InternalMiniJava.g:420:3: ( rule__Return__Group__0 )
            // InternalMiniJava.g:420:4: rule__Return__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__Return__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getReturnAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleReturn"


    // $ANTLR start "entryRuleIfStatement"
    // InternalMiniJava.g:429:1: entryRuleIfStatement : ruleIfStatement EOF ;
    public final void entryRuleIfStatement() throws RecognitionException {
        try {
            // InternalMiniJava.g:430:1: ( ruleIfStatement EOF )
            // InternalMiniJava.g:431:1: ruleIfStatement EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getIfStatementRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleIfStatement();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getIfStatementRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleIfStatement"


    // $ANTLR start "ruleIfStatement"
    // InternalMiniJava.g:438:1: ruleIfStatement : ( ( rule__IfStatement__Group__0 ) ) ;
    public final void ruleIfStatement() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:442:2: ( ( ( rule__IfStatement__Group__0 ) ) )
            // InternalMiniJava.g:443:2: ( ( rule__IfStatement__Group__0 ) )
            {
            // InternalMiniJava.g:443:2: ( ( rule__IfStatement__Group__0 ) )
            // InternalMiniJava.g:444:3: ( rule__IfStatement__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getIfStatementAccess().getGroup()); 
            }
            // InternalMiniJava.g:445:3: ( rule__IfStatement__Group__0 )
            // InternalMiniJava.g:445:4: rule__IfStatement__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__IfStatement__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getIfStatementAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleIfStatement"


    // $ANTLR start "entryRuleWhileStatement"
    // InternalMiniJava.g:454:1: entryRuleWhileStatement : ruleWhileStatement EOF ;
    public final void entryRuleWhileStatement() throws RecognitionException {
        try {
            // InternalMiniJava.g:455:1: ( ruleWhileStatement EOF )
            // InternalMiniJava.g:456:1: ruleWhileStatement EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getWhileStatementRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleWhileStatement();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getWhileStatementRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleWhileStatement"


    // $ANTLR start "ruleWhileStatement"
    // InternalMiniJava.g:463:1: ruleWhileStatement : ( ( rule__WhileStatement__Group__0 ) ) ;
    public final void ruleWhileStatement() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:467:2: ( ( ( rule__WhileStatement__Group__0 ) ) )
            // InternalMiniJava.g:468:2: ( ( rule__WhileStatement__Group__0 ) )
            {
            // InternalMiniJava.g:468:2: ( ( rule__WhileStatement__Group__0 ) )
            // InternalMiniJava.g:469:3: ( rule__WhileStatement__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getWhileStatementAccess().getGroup()); 
            }
            // InternalMiniJava.g:470:3: ( rule__WhileStatement__Group__0 )
            // InternalMiniJava.g:470:4: rule__WhileStatement__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__WhileStatement__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getWhileStatementAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleWhileStatement"


    // $ANTLR start "entryRuleForStatement"
    // InternalMiniJava.g:479:1: entryRuleForStatement : ruleForStatement EOF ;
    public final void entryRuleForStatement() throws RecognitionException {
        try {
            // InternalMiniJava.g:480:1: ( ruleForStatement EOF )
            // InternalMiniJava.g:481:1: ruleForStatement EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getForStatementRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleForStatement();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getForStatementRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleForStatement"


    // $ANTLR start "ruleForStatement"
    // InternalMiniJava.g:488:1: ruleForStatement : ( ( rule__ForStatement__Group__0 ) ) ;
    public final void ruleForStatement() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:492:2: ( ( ( rule__ForStatement__Group__0 ) ) )
            // InternalMiniJava.g:493:2: ( ( rule__ForStatement__Group__0 ) )
            {
            // InternalMiniJava.g:493:2: ( ( rule__ForStatement__Group__0 ) )
            // InternalMiniJava.g:494:3: ( rule__ForStatement__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getForStatementAccess().getGroup()); 
            }
            // InternalMiniJava.g:495:3: ( rule__ForStatement__Group__0 )
            // InternalMiniJava.g:495:4: rule__ForStatement__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__ForStatement__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getForStatementAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleForStatement"


    // $ANTLR start "entryRuleTypeRef"
    // InternalMiniJava.g:504:1: entryRuleTypeRef : ruleTypeRef EOF ;
    public final void entryRuleTypeRef() throws RecognitionException {
        try {
            // InternalMiniJava.g:505:1: ( ruleTypeRef EOF )
            // InternalMiniJava.g:506:1: ruleTypeRef EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTypeRefRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleTypeRef();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTypeRefRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleTypeRef"


    // $ANTLR start "ruleTypeRef"
    // InternalMiniJava.g:513:1: ruleTypeRef : ( ( rule__TypeRef__Group__0 ) ) ;
    public final void ruleTypeRef() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:517:2: ( ( ( rule__TypeRef__Group__0 ) ) )
            // InternalMiniJava.g:518:2: ( ( rule__TypeRef__Group__0 ) )
            {
            // InternalMiniJava.g:518:2: ( ( rule__TypeRef__Group__0 ) )
            // InternalMiniJava.g:519:3: ( rule__TypeRef__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTypeRefAccess().getGroup()); 
            }
            // InternalMiniJava.g:520:3: ( rule__TypeRef__Group__0 )
            // InternalMiniJava.g:520:4: rule__TypeRef__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__TypeRef__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTypeRefAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleTypeRef"


    // $ANTLR start "entryRuleSingleTypeRef"
    // InternalMiniJava.g:529:1: entryRuleSingleTypeRef : ruleSingleTypeRef EOF ;
    public final void entryRuleSingleTypeRef() throws RecognitionException {
        try {
            // InternalMiniJava.g:530:1: ( ruleSingleTypeRef EOF )
            // InternalMiniJava.g:531:1: ruleSingleTypeRef EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSingleTypeRefRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleSingleTypeRef();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getSingleTypeRefRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleSingleTypeRef"


    // $ANTLR start "ruleSingleTypeRef"
    // InternalMiniJava.g:538:1: ruleSingleTypeRef : ( ( rule__SingleTypeRef__Alternatives ) ) ;
    public final void ruleSingleTypeRef() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:542:2: ( ( ( rule__SingleTypeRef__Alternatives ) ) )
            // InternalMiniJava.g:543:2: ( ( rule__SingleTypeRef__Alternatives ) )
            {
            // InternalMiniJava.g:543:2: ( ( rule__SingleTypeRef__Alternatives ) )
            // InternalMiniJava.g:544:3: ( rule__SingleTypeRef__Alternatives )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSingleTypeRefAccess().getAlternatives()); 
            }
            // InternalMiniJava.g:545:3: ( rule__SingleTypeRef__Alternatives )
            // InternalMiniJava.g:545:4: rule__SingleTypeRef__Alternatives
            {
            pushFollow(FOLLOW_2);
            rule__SingleTypeRef__Alternatives();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getSingleTypeRefAccess().getAlternatives()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleSingleTypeRef"


    // $ANTLR start "entryRuleClassRef"
    // InternalMiniJava.g:554:1: entryRuleClassRef : ruleClassRef EOF ;
    public final void entryRuleClassRef() throws RecognitionException {
        try {
            // InternalMiniJava.g:555:1: ( ruleClassRef EOF )
            // InternalMiniJava.g:556:1: ruleClassRef EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassRefRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleClassRef();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassRefRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleClassRef"


    // $ANTLR start "ruleClassRef"
    // InternalMiniJava.g:563:1: ruleClassRef : ( ( rule__ClassRef__ReferencedClassAssignment ) ) ;
    public final void ruleClassRef() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:567:2: ( ( ( rule__ClassRef__ReferencedClassAssignment ) ) )
            // InternalMiniJava.g:568:2: ( ( rule__ClassRef__ReferencedClassAssignment ) )
            {
            // InternalMiniJava.g:568:2: ( ( rule__ClassRef__ReferencedClassAssignment ) )
            // InternalMiniJava.g:569:3: ( rule__ClassRef__ReferencedClassAssignment )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassRefAccess().getReferencedClassAssignment()); 
            }
            // InternalMiniJava.g:570:3: ( rule__ClassRef__ReferencedClassAssignment )
            // InternalMiniJava.g:570:4: rule__ClassRef__ReferencedClassAssignment
            {
            pushFollow(FOLLOW_2);
            rule__ClassRef__ReferencedClassAssignment();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassRefAccess().getReferencedClassAssignment()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleClassRef"


    // $ANTLR start "entryRuleTypedDeclaration"
    // InternalMiniJava.g:579:1: entryRuleTypedDeclaration : ruleTypedDeclaration EOF ;
    public final void entryRuleTypedDeclaration() throws RecognitionException {
        try {
            // InternalMiniJava.g:580:1: ( ruleTypedDeclaration EOF )
            // InternalMiniJava.g:581:1: ruleTypedDeclaration EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTypedDeclarationRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleTypedDeclaration();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTypedDeclarationRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleTypedDeclaration"


    // $ANTLR start "ruleTypedDeclaration"
    // InternalMiniJava.g:588:1: ruleTypedDeclaration : ( ( rule__TypedDeclaration__Alternatives ) ) ;
    public final void ruleTypedDeclaration() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:592:2: ( ( ( rule__TypedDeclaration__Alternatives ) ) )
            // InternalMiniJava.g:593:2: ( ( rule__TypedDeclaration__Alternatives ) )
            {
            // InternalMiniJava.g:593:2: ( ( rule__TypedDeclaration__Alternatives ) )
            // InternalMiniJava.g:594:3: ( rule__TypedDeclaration__Alternatives )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTypedDeclarationAccess().getAlternatives()); 
            }
            // InternalMiniJava.g:595:3: ( rule__TypedDeclaration__Alternatives )
            // InternalMiniJava.g:595:4: rule__TypedDeclaration__Alternatives
            {
            pushFollow(FOLLOW_2);
            rule__TypedDeclaration__Alternatives();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTypedDeclarationAccess().getAlternatives()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleTypedDeclaration"


    // $ANTLR start "entryRuleSymbol"
    // InternalMiniJava.g:604:1: entryRuleSymbol : ruleSymbol EOF ;
    public final void entryRuleSymbol() throws RecognitionException {
        try {
            // InternalMiniJava.g:605:1: ( ruleSymbol EOF )
            // InternalMiniJava.g:606:1: ruleSymbol EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSymbolRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleSymbol();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getSymbolRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleSymbol"


    // $ANTLR start "ruleSymbol"
    // InternalMiniJava.g:613:1: ruleSymbol : ( ( rule__Symbol__Alternatives ) ) ;
    public final void ruleSymbol() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:617:2: ( ( ( rule__Symbol__Alternatives ) ) )
            // InternalMiniJava.g:618:2: ( ( rule__Symbol__Alternatives ) )
            {
            // InternalMiniJava.g:618:2: ( ( rule__Symbol__Alternatives ) )
            // InternalMiniJava.g:619:3: ( rule__Symbol__Alternatives )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSymbolAccess().getAlternatives()); 
            }
            // InternalMiniJava.g:620:3: ( rule__Symbol__Alternatives )
            // InternalMiniJava.g:620:4: rule__Symbol__Alternatives
            {
            pushFollow(FOLLOW_2);
            rule__Symbol__Alternatives();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getSymbolAccess().getAlternatives()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleSymbol"


    // $ANTLR start "entryRuleVariableDeclaration"
    // InternalMiniJava.g:629:1: entryRuleVariableDeclaration : ruleVariableDeclaration EOF ;
    public final void entryRuleVariableDeclaration() throws RecognitionException {
        try {
            // InternalMiniJava.g:630:1: ( ruleVariableDeclaration EOF )
            // InternalMiniJava.g:631:1: ruleVariableDeclaration EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getVariableDeclarationRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleVariableDeclaration();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getVariableDeclarationRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleVariableDeclaration"


    // $ANTLR start "ruleVariableDeclaration"
    // InternalMiniJava.g:638:1: ruleVariableDeclaration : ( ( rule__VariableDeclaration__Group__0 ) ) ;
    public final void ruleVariableDeclaration() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:642:2: ( ( ( rule__VariableDeclaration__Group__0 ) ) )
            // InternalMiniJava.g:643:2: ( ( rule__VariableDeclaration__Group__0 ) )
            {
            // InternalMiniJava.g:643:2: ( ( rule__VariableDeclaration__Group__0 ) )
            // InternalMiniJava.g:644:3: ( rule__VariableDeclaration__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getVariableDeclarationAccess().getGroup()); 
            }
            // InternalMiniJava.g:645:3: ( rule__VariableDeclaration__Group__0 )
            // InternalMiniJava.g:645:4: rule__VariableDeclaration__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__VariableDeclaration__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getVariableDeclarationAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleVariableDeclaration"


    // $ANTLR start "entryRuleAssignment"
    // InternalMiniJava.g:654:1: entryRuleAssignment : ruleAssignment EOF ;
    public final void entryRuleAssignment() throws RecognitionException {
        try {
            // InternalMiniJava.g:655:1: ( ruleAssignment EOF )
            // InternalMiniJava.g:656:1: ruleAssignment EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getAssignmentRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleAssignment();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getAssignmentRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleAssignment"


    // $ANTLR start "ruleAssignment"
    // InternalMiniJava.g:663:1: ruleAssignment : ( ( rule__Assignment__Group__0 ) ) ;
    public final void ruleAssignment() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:667:2: ( ( ( rule__Assignment__Group__0 ) ) )
            // InternalMiniJava.g:668:2: ( ( rule__Assignment__Group__0 ) )
            {
            // InternalMiniJava.g:668:2: ( ( rule__Assignment__Group__0 ) )
            // InternalMiniJava.g:669:3: ( rule__Assignment__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getAssignmentAccess().getGroup()); 
            }
            // InternalMiniJava.g:670:3: ( rule__Assignment__Group__0 )
            // InternalMiniJava.g:670:4: rule__Assignment__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__Assignment__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getAssignmentAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleAssignment"


    // $ANTLR start "entryRuleAssignee"
    // InternalMiniJava.g:679:1: entryRuleAssignee : ruleAssignee EOF ;
    public final void entryRuleAssignee() throws RecognitionException {
        try {
            // InternalMiniJava.g:680:1: ( ruleAssignee EOF )
            // InternalMiniJava.g:681:1: ruleAssignee EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getAssigneeRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleAssignee();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getAssigneeRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleAssignee"


    // $ANTLR start "ruleAssignee"
    // InternalMiniJava.g:688:1: ruleAssignee : ( ( rule__Assignee__Alternatives ) ) ;
    public final void ruleAssignee() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:692:2: ( ( ( rule__Assignee__Alternatives ) ) )
            // InternalMiniJava.g:693:2: ( ( rule__Assignee__Alternatives ) )
            {
            // InternalMiniJava.g:693:2: ( ( rule__Assignee__Alternatives ) )
            // InternalMiniJava.g:694:3: ( rule__Assignee__Alternatives )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getAssigneeAccess().getAlternatives()); 
            }
            // InternalMiniJava.g:695:3: ( rule__Assignee__Alternatives )
            // InternalMiniJava.g:695:4: rule__Assignee__Alternatives
            {
            pushFollow(FOLLOW_2);
            rule__Assignee__Alternatives();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getAssigneeAccess().getAlternatives()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleAssignee"


    // $ANTLR start "entryRuleExpression"
    // InternalMiniJava.g:704:1: entryRuleExpression : ruleExpression EOF ;
    public final void entryRuleExpression() throws RecognitionException {
        try {
            // InternalMiniJava.g:705:1: ( ruleExpression EOF )
            // InternalMiniJava.g:706:1: ruleExpression EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getExpressionRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleExpression();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getExpressionRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleExpression"


    // $ANTLR start "ruleExpression"
    // InternalMiniJava.g:713:1: ruleExpression : ( ruleOr ) ;
    public final void ruleExpression() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:717:2: ( ( ruleOr ) )
            // InternalMiniJava.g:718:2: ( ruleOr )
            {
            // InternalMiniJava.g:718:2: ( ruleOr )
            // InternalMiniJava.g:719:3: ruleOr
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getExpressionAccess().getOrParserRuleCall()); 
            }
            pushFollow(FOLLOW_2);
            ruleOr();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getExpressionAccess().getOrParserRuleCall()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleExpression"


    // $ANTLR start "entryRuleOr"
    // InternalMiniJava.g:729:1: entryRuleOr : ruleOr EOF ;
    public final void entryRuleOr() throws RecognitionException {
        try {
            // InternalMiniJava.g:730:1: ( ruleOr EOF )
            // InternalMiniJava.g:731:1: ruleOr EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getOrRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleOr();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getOrRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleOr"


    // $ANTLR start "ruleOr"
    // InternalMiniJava.g:738:1: ruleOr : ( ( rule__Or__Group__0 ) ) ;
    public final void ruleOr() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:742:2: ( ( ( rule__Or__Group__0 ) ) )
            // InternalMiniJava.g:743:2: ( ( rule__Or__Group__0 ) )
            {
            // InternalMiniJava.g:743:2: ( ( rule__Or__Group__0 ) )
            // InternalMiniJava.g:744:3: ( rule__Or__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getOrAccess().getGroup()); 
            }
            // InternalMiniJava.g:745:3: ( rule__Or__Group__0 )
            // InternalMiniJava.g:745:4: rule__Or__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__Or__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getOrAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleOr"


    // $ANTLR start "entryRuleAnd"
    // InternalMiniJava.g:754:1: entryRuleAnd : ruleAnd EOF ;
    public final void entryRuleAnd() throws RecognitionException {
        try {
            // InternalMiniJava.g:755:1: ( ruleAnd EOF )
            // InternalMiniJava.g:756:1: ruleAnd EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getAndRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleAnd();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getAndRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleAnd"


    // $ANTLR start "ruleAnd"
    // InternalMiniJava.g:763:1: ruleAnd : ( ( rule__And__Group__0 ) ) ;
    public final void ruleAnd() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:767:2: ( ( ( rule__And__Group__0 ) ) )
            // InternalMiniJava.g:768:2: ( ( rule__And__Group__0 ) )
            {
            // InternalMiniJava.g:768:2: ( ( rule__And__Group__0 ) )
            // InternalMiniJava.g:769:3: ( rule__And__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getAndAccess().getGroup()); 
            }
            // InternalMiniJava.g:770:3: ( rule__And__Group__0 )
            // InternalMiniJava.g:770:4: rule__And__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__And__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getAndAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleAnd"


    // $ANTLR start "entryRuleEquality"
    // InternalMiniJava.g:779:1: entryRuleEquality : ruleEquality EOF ;
    public final void entryRuleEquality() throws RecognitionException {
        try {
            // InternalMiniJava.g:780:1: ( ruleEquality EOF )
            // InternalMiniJava.g:781:1: ruleEquality EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getEqualityRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleEquality();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getEqualityRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleEquality"


    // $ANTLR start "ruleEquality"
    // InternalMiniJava.g:788:1: ruleEquality : ( ( rule__Equality__Group__0 ) ) ;
    public final void ruleEquality() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:792:2: ( ( ( rule__Equality__Group__0 ) ) )
            // InternalMiniJava.g:793:2: ( ( rule__Equality__Group__0 ) )
            {
            // InternalMiniJava.g:793:2: ( ( rule__Equality__Group__0 ) )
            // InternalMiniJava.g:794:3: ( rule__Equality__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getEqualityAccess().getGroup()); 
            }
            // InternalMiniJava.g:795:3: ( rule__Equality__Group__0 )
            // InternalMiniJava.g:795:4: rule__Equality__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__Equality__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getEqualityAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleEquality"


    // $ANTLR start "entryRuleComparison"
    // InternalMiniJava.g:804:1: entryRuleComparison : ruleComparison EOF ;
    public final void entryRuleComparison() throws RecognitionException {
        try {
            // InternalMiniJava.g:805:1: ( ruleComparison EOF )
            // InternalMiniJava.g:806:1: ruleComparison EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getComparisonRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleComparison();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getComparisonRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleComparison"


    // $ANTLR start "ruleComparison"
    // InternalMiniJava.g:813:1: ruleComparison : ( ( rule__Comparison__Group__0 ) ) ;
    public final void ruleComparison() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:817:2: ( ( ( rule__Comparison__Group__0 ) ) )
            // InternalMiniJava.g:818:2: ( ( rule__Comparison__Group__0 ) )
            {
            // InternalMiniJava.g:818:2: ( ( rule__Comparison__Group__0 ) )
            // InternalMiniJava.g:819:3: ( rule__Comparison__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getComparisonAccess().getGroup()); 
            }
            // InternalMiniJava.g:820:3: ( rule__Comparison__Group__0 )
            // InternalMiniJava.g:820:4: rule__Comparison__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__Comparison__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getComparisonAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleComparison"


    // $ANTLR start "entryRulePlusOrMinus"
    // InternalMiniJava.g:829:1: entryRulePlusOrMinus : rulePlusOrMinus EOF ;
    public final void entryRulePlusOrMinus() throws RecognitionException {
        try {
            // InternalMiniJava.g:830:1: ( rulePlusOrMinus EOF )
            // InternalMiniJava.g:831:1: rulePlusOrMinus EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPlusOrMinusRule()); 
            }
            pushFollow(FOLLOW_1);
            rulePlusOrMinus();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getPlusOrMinusRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRulePlusOrMinus"


    // $ANTLR start "rulePlusOrMinus"
    // InternalMiniJava.g:838:1: rulePlusOrMinus : ( ( rule__PlusOrMinus__Group__0 ) ) ;
    public final void rulePlusOrMinus() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:842:2: ( ( ( rule__PlusOrMinus__Group__0 ) ) )
            // InternalMiniJava.g:843:2: ( ( rule__PlusOrMinus__Group__0 ) )
            {
            // InternalMiniJava.g:843:2: ( ( rule__PlusOrMinus__Group__0 ) )
            // InternalMiniJava.g:844:3: ( rule__PlusOrMinus__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPlusOrMinusAccess().getGroup()); 
            }
            // InternalMiniJava.g:845:3: ( rule__PlusOrMinus__Group__0 )
            // InternalMiniJava.g:845:4: rule__PlusOrMinus__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__PlusOrMinus__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getPlusOrMinusAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rulePlusOrMinus"


    // $ANTLR start "entryRuleMulOrDiv"
    // InternalMiniJava.g:854:1: entryRuleMulOrDiv : ruleMulOrDiv EOF ;
    public final void entryRuleMulOrDiv() throws RecognitionException {
        try {
            // InternalMiniJava.g:855:1: ( ruleMulOrDiv EOF )
            // InternalMiniJava.g:856:1: ruleMulOrDiv EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMulOrDivRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleMulOrDiv();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getMulOrDivRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleMulOrDiv"


    // $ANTLR start "ruleMulOrDiv"
    // InternalMiniJava.g:863:1: ruleMulOrDiv : ( ( rule__MulOrDiv__Group__0 ) ) ;
    public final void ruleMulOrDiv() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:867:2: ( ( ( rule__MulOrDiv__Group__0 ) ) )
            // InternalMiniJava.g:868:2: ( ( rule__MulOrDiv__Group__0 ) )
            {
            // InternalMiniJava.g:868:2: ( ( rule__MulOrDiv__Group__0 ) )
            // InternalMiniJava.g:869:3: ( rule__MulOrDiv__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMulOrDivAccess().getGroup()); 
            }
            // InternalMiniJava.g:870:3: ( rule__MulOrDiv__Group__0 )
            // InternalMiniJava.g:870:4: rule__MulOrDiv__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__MulOrDiv__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getMulOrDivAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleMulOrDiv"


    // $ANTLR start "entryRuleArrayAccess"
    // InternalMiniJava.g:879:1: entryRuleArrayAccess : ruleArrayAccess EOF ;
    public final void entryRuleArrayAccess() throws RecognitionException {
        try {
            // InternalMiniJava.g:880:1: ( ruleArrayAccess EOF )
            // InternalMiniJava.g:881:1: ruleArrayAccess EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getArrayAccessRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleArrayAccess();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getArrayAccessRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleArrayAccess"


    // $ANTLR start "ruleArrayAccess"
    // InternalMiniJava.g:888:1: ruleArrayAccess : ( ( rule__ArrayAccess__Group__0 ) ) ;
    public final void ruleArrayAccess() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:892:2: ( ( ( rule__ArrayAccess__Group__0 ) ) )
            // InternalMiniJava.g:893:2: ( ( rule__ArrayAccess__Group__0 ) )
            {
            // InternalMiniJava.g:893:2: ( ( rule__ArrayAccess__Group__0 ) )
            // InternalMiniJava.g:894:3: ( rule__ArrayAccess__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getArrayAccessAccess().getGroup()); 
            }
            // InternalMiniJava.g:895:3: ( rule__ArrayAccess__Group__0 )
            // InternalMiniJava.g:895:4: rule__ArrayAccess__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__ArrayAccess__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getArrayAccessAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleArrayAccess"


    // $ANTLR start "entryRuleArrayLength"
    // InternalMiniJava.g:904:1: entryRuleArrayLength : ruleArrayLength EOF ;
    public final void entryRuleArrayLength() throws RecognitionException {
        try {
            // InternalMiniJava.g:905:1: ( ruleArrayLength EOF )
            // InternalMiniJava.g:906:1: ruleArrayLength EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getArrayLengthRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleArrayLength();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getArrayLengthRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleArrayLength"


    // $ANTLR start "ruleArrayLength"
    // InternalMiniJava.g:913:1: ruleArrayLength : ( ( rule__ArrayLength__Group__0 ) ) ;
    public final void ruleArrayLength() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:917:2: ( ( ( rule__ArrayLength__Group__0 ) ) )
            // InternalMiniJava.g:918:2: ( ( rule__ArrayLength__Group__0 ) )
            {
            // InternalMiniJava.g:918:2: ( ( rule__ArrayLength__Group__0 ) )
            // InternalMiniJava.g:919:3: ( rule__ArrayLength__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getArrayLengthAccess().getGroup()); 
            }
            // InternalMiniJava.g:920:3: ( rule__ArrayLength__Group__0 )
            // InternalMiniJava.g:920:4: rule__ArrayLength__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__ArrayLength__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getArrayLengthAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleArrayLength"


    // $ANTLR start "entryRulePrimary"
    // InternalMiniJava.g:929:1: entryRulePrimary : rulePrimary EOF ;
    public final void entryRulePrimary() throws RecognitionException {
        try {
            // InternalMiniJava.g:930:1: ( rulePrimary EOF )
            // InternalMiniJava.g:931:1: rulePrimary EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrimaryRule()); 
            }
            pushFollow(FOLLOW_1);
            rulePrimary();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrimaryRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRulePrimary"


    // $ANTLR start "rulePrimary"
    // InternalMiniJava.g:938:1: rulePrimary : ( ( rule__Primary__Alternatives ) ) ;
    public final void rulePrimary() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:942:2: ( ( ( rule__Primary__Alternatives ) ) )
            // InternalMiniJava.g:943:2: ( ( rule__Primary__Alternatives ) )
            {
            // InternalMiniJava.g:943:2: ( ( rule__Primary__Alternatives ) )
            // InternalMiniJava.g:944:3: ( rule__Primary__Alternatives )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrimaryAccess().getAlternatives()); 
            }
            // InternalMiniJava.g:945:3: ( rule__Primary__Alternatives )
            // InternalMiniJava.g:945:4: rule__Primary__Alternatives
            {
            pushFollow(FOLLOW_2);
            rule__Primary__Alternatives();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrimaryAccess().getAlternatives()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rulePrimary"


    // $ANTLR start "entryRuleSelectionExpression"
    // InternalMiniJava.g:954:1: entryRuleSelectionExpression : ruleSelectionExpression EOF ;
    public final void entryRuleSelectionExpression() throws RecognitionException {
        try {
            // InternalMiniJava.g:955:1: ( ruleSelectionExpression EOF )
            // InternalMiniJava.g:956:1: ruleSelectionExpression EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleSelectionExpression();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleSelectionExpression"


    // $ANTLR start "ruleSelectionExpression"
    // InternalMiniJava.g:963:1: ruleSelectionExpression : ( ( rule__SelectionExpression__Group__0 ) ) ;
    public final void ruleSelectionExpression() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:967:2: ( ( ( rule__SelectionExpression__Group__0 ) ) )
            // InternalMiniJava.g:968:2: ( ( rule__SelectionExpression__Group__0 ) )
            {
            // InternalMiniJava.g:968:2: ( ( rule__SelectionExpression__Group__0 ) )
            // InternalMiniJava.g:969:3: ( rule__SelectionExpression__Group__0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionAccess().getGroup()); 
            }
            // InternalMiniJava.g:970:3: ( rule__SelectionExpression__Group__0 )
            // InternalMiniJava.g:970:4: rule__SelectionExpression__Group__0
            {
            pushFollow(FOLLOW_2);
            rule__SelectionExpression__Group__0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionAccess().getGroup()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleSelectionExpression"


    // $ANTLR start "entryRuleTerminalExpression"
    // InternalMiniJava.g:979:1: entryRuleTerminalExpression : ruleTerminalExpression EOF ;
    public final void entryRuleTerminalExpression() throws RecognitionException {
        try {
            // InternalMiniJava.g:980:1: ( ruleTerminalExpression EOF )
            // InternalMiniJava.g:981:1: ruleTerminalExpression EOF
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionRule()); 
            }
            pushFollow(FOLLOW_1);
            ruleTerminalExpression();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionRule()); 
            }
            match(input,EOF,FOLLOW_2); if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "entryRuleTerminalExpression"


    // $ANTLR start "ruleTerminalExpression"
    // InternalMiniJava.g:988:1: ruleTerminalExpression : ( ( rule__TerminalExpression__Alternatives ) ) ;
    public final void ruleTerminalExpression() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:992:2: ( ( ( rule__TerminalExpression__Alternatives ) ) )
            // InternalMiniJava.g:993:2: ( ( rule__TerminalExpression__Alternatives ) )
            {
            // InternalMiniJava.g:993:2: ( ( rule__TerminalExpression__Alternatives ) )
            // InternalMiniJava.g:994:3: ( rule__TerminalExpression__Alternatives )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getAlternatives()); 
            }
            // InternalMiniJava.g:995:3: ( rule__TerminalExpression__Alternatives )
            // InternalMiniJava.g:995:4: rule__TerminalExpression__Alternatives
            {
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Alternatives();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getAlternatives()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleTerminalExpression"


    // $ANTLR start "ruleAccessLevel"
    // InternalMiniJava.g:1004:1: ruleAccessLevel : ( ( rule__AccessLevel__Alternatives ) ) ;
    public final void ruleAccessLevel() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1008:1: ( ( ( rule__AccessLevel__Alternatives ) ) )
            // InternalMiniJava.g:1009:2: ( ( rule__AccessLevel__Alternatives ) )
            {
            // InternalMiniJava.g:1009:2: ( ( rule__AccessLevel__Alternatives ) )
            // InternalMiniJava.g:1010:3: ( rule__AccessLevel__Alternatives )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getAccessLevelAccess().getAlternatives()); 
            }
            // InternalMiniJava.g:1011:3: ( rule__AccessLevel__Alternatives )
            // InternalMiniJava.g:1011:4: rule__AccessLevel__Alternatives
            {
            pushFollow(FOLLOW_2);
            rule__AccessLevel__Alternatives();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getAccessLevelAccess().getAlternatives()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "ruleAccessLevel"


    // $ANTLR start "rule__TypeDeclaration__Alternatives"
    // InternalMiniJava.g:1019:1: rule__TypeDeclaration__Alternatives : ( ( ruleClass ) | ( ruleInterface ) );
    public final void rule__TypeDeclaration__Alternatives() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1023:1: ( ( ruleClass ) | ( ruleInterface ) )
            int alt1=2;
            switch ( input.LA(1) ) {
            case 14:
                {
                int LA1_1 = input.LA(2);

                if ( (LA1_1==21||LA1_1==63) ) {
                    alt1=1;
                }
                else if ( (LA1_1==27) ) {
                    alt1=2;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return ;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 1, 1, input);

                    throw nvae;
                }
                }
                break;
            case 15:
                {
                int LA1_2 = input.LA(2);

                if ( (LA1_2==21||LA1_2==63) ) {
                    alt1=1;
                }
                else if ( (LA1_2==27) ) {
                    alt1=2;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return ;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 1, 2, input);

                    throw nvae;
                }
                }
                break;
            case 16:
                {
                int LA1_3 = input.LA(2);

                if ( (LA1_3==21||LA1_3==63) ) {
                    alt1=1;
                }
                else if ( (LA1_3==27) ) {
                    alt1=2;
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return ;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 1, 3, input);

                    throw nvae;
                }
                }
                break;
            case 21:
            case 63:
                {
                alt1=1;
                }
                break;
            case 27:
                {
                alt1=2;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return ;}
                NoViableAltException nvae =
                    new NoViableAltException("", 1, 0, input);

                throw nvae;
            }

            switch (alt1) {
                case 1 :
                    // InternalMiniJava.g:1024:2: ( ruleClass )
                    {
                    // InternalMiniJava.g:1024:2: ( ruleClass )
                    // InternalMiniJava.g:1025:3: ruleClass
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getTypeDeclarationAccess().getClassParserRuleCall_0()); 
                    }
                    pushFollow(FOLLOW_2);
                    ruleClass();

                    state._fsp--;
                    if (state.failed) return ;
                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getTypeDeclarationAccess().getClassParserRuleCall_0()); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalMiniJava.g:1030:2: ( ruleInterface )
                    {
                    // InternalMiniJava.g:1030:2: ( ruleInterface )
                    // InternalMiniJava.g:1031:3: ruleInterface
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getTypeDeclarationAccess().getInterfaceParserRuleCall_1()); 
                    }
                    pushFollow(FOLLOW_2);
                    ruleInterface();

                    state._fsp--;
                    if (state.failed) return ;
                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getTypeDeclarationAccess().getInterfaceParserRuleCall_1()); 
                    }

                    }


                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TypeDeclaration__Alternatives"


    // $ANTLR start "rule__Member__Alternatives"
    // InternalMiniJava.g:1040:1: rule__Member__Alternatives : ( ( ruleField ) | ( ruleMethod ) );
    public final void rule__Member__Alternatives() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1044:1: ( ( ruleField ) | ( ruleMethod ) )
            int alt2=2;
            alt2 = dfa2.predict(input);
            switch (alt2) {
                case 1 :
                    // InternalMiniJava.g:1045:2: ( ruleField )
                    {
                    // InternalMiniJava.g:1045:2: ( ruleField )
                    // InternalMiniJava.g:1046:3: ruleField
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getMemberAccess().getFieldParserRuleCall_0()); 
                    }
                    pushFollow(FOLLOW_2);
                    ruleField();

                    state._fsp--;
                    if (state.failed) return ;
                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getMemberAccess().getFieldParserRuleCall_0()); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalMiniJava.g:1051:2: ( ruleMethod )
                    {
                    // InternalMiniJava.g:1051:2: ( ruleMethod )
                    // InternalMiniJava.g:1052:3: ruleMethod
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getMemberAccess().getMethodParserRuleCall_1()); 
                    }
                    pushFollow(FOLLOW_2);
                    ruleMethod();

                    state._fsp--;
                    if (state.failed) return ;
                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getMemberAccess().getMethodParserRuleCall_1()); 
                    }

                    }


                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Member__Alternatives"


    // $ANTLR start "rule__Method__Alternatives_8"
    // InternalMiniJava.g:1061:1: rule__Method__Alternatives_8 : ( ( ( rule__Method__BodyAssignment_8_0 ) ) | ( ';' ) );
    public final void rule__Method__Alternatives_8() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1065:1: ( ( ( rule__Method__BodyAssignment_8_0 ) ) | ( ';' ) )
            int alt3=2;
            int LA3_0 = input.LA(1);

            if ( (LA3_0==22) ) {
                alt3=1;
            }
            else if ( (LA3_0==11) ) {
                alt3=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return ;}
                NoViableAltException nvae =
                    new NoViableAltException("", 3, 0, input);

                throw nvae;
            }
            switch (alt3) {
                case 1 :
                    // InternalMiniJava.g:1066:2: ( ( rule__Method__BodyAssignment_8_0 ) )
                    {
                    // InternalMiniJava.g:1066:2: ( ( rule__Method__BodyAssignment_8_0 ) )
                    // InternalMiniJava.g:1067:3: ( rule__Method__BodyAssignment_8_0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getMethodAccess().getBodyAssignment_8_0()); 
                    }
                    // InternalMiniJava.g:1068:3: ( rule__Method__BodyAssignment_8_0 )
                    // InternalMiniJava.g:1068:4: rule__Method__BodyAssignment_8_0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Method__BodyAssignment_8_0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getMethodAccess().getBodyAssignment_8_0()); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalMiniJava.g:1072:2: ( ';' )
                    {
                    // InternalMiniJava.g:1072:2: ( ';' )
                    // InternalMiniJava.g:1073:3: ';'
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getMethodAccess().getSemicolonKeyword_8_1()); 
                    }
                    match(input,11,FOLLOW_2); if (state.failed) return ;
                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getMethodAccess().getSemicolonKeyword_8_1()); 
                    }

                    }


                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Alternatives_8"


    // $ANTLR start "rule__Statement__Alternatives"
    // InternalMiniJava.g:1082:1: rule__Statement__Alternatives : ( ( ( rule__Statement__Group_0__0 ) ) | ( ( rule__Statement__Group_1__0 ) ) | ( ruleIfStatement ) | ( ruleWhileStatement ) | ( ruleForStatement ) | ( ( rule__Statement__Group_5__0 ) ) | ( ruleBlock ) | ( ( rule__Statement__Group_7__0 ) ) );
    public final void rule__Statement__Alternatives() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1086:1: ( ( ( rule__Statement__Group_0__0 ) ) | ( ( rule__Statement__Group_1__0 ) ) | ( ruleIfStatement ) | ( ruleWhileStatement ) | ( ruleForStatement ) | ( ( rule__Statement__Group_5__0 ) ) | ( ruleBlock ) | ( ( rule__Statement__Group_7__0 ) ) )
            int alt4=8;
            alt4 = dfa4.predict(input);
            switch (alt4) {
                case 1 :
                    // InternalMiniJava.g:1087:2: ( ( rule__Statement__Group_0__0 ) )
                    {
                    // InternalMiniJava.g:1087:2: ( ( rule__Statement__Group_0__0 ) )
                    // InternalMiniJava.g:1088:3: ( rule__Statement__Group_0__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getStatementAccess().getGroup_0()); 
                    }
                    // InternalMiniJava.g:1089:3: ( rule__Statement__Group_0__0 )
                    // InternalMiniJava.g:1089:4: rule__Statement__Group_0__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Statement__Group_0__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getStatementAccess().getGroup_0()); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalMiniJava.g:1093:2: ( ( rule__Statement__Group_1__0 ) )
                    {
                    // InternalMiniJava.g:1093:2: ( ( rule__Statement__Group_1__0 ) )
                    // InternalMiniJava.g:1094:3: ( rule__Statement__Group_1__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getStatementAccess().getGroup_1()); 
                    }
                    // InternalMiniJava.g:1095:3: ( rule__Statement__Group_1__0 )
                    // InternalMiniJava.g:1095:4: rule__Statement__Group_1__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Statement__Group_1__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getStatementAccess().getGroup_1()); 
                    }

                    }


                    }
                    break;
                case 3 :
                    // InternalMiniJava.g:1099:2: ( ruleIfStatement )
                    {
                    // InternalMiniJava.g:1099:2: ( ruleIfStatement )
                    // InternalMiniJava.g:1100:3: ruleIfStatement
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getStatementAccess().getIfStatementParserRuleCall_2()); 
                    }
                    pushFollow(FOLLOW_2);
                    ruleIfStatement();

                    state._fsp--;
                    if (state.failed) return ;
                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getStatementAccess().getIfStatementParserRuleCall_2()); 
                    }

                    }


                    }
                    break;
                case 4 :
                    // InternalMiniJava.g:1105:2: ( ruleWhileStatement )
                    {
                    // InternalMiniJava.g:1105:2: ( ruleWhileStatement )
                    // InternalMiniJava.g:1106:3: ruleWhileStatement
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getStatementAccess().getWhileStatementParserRuleCall_3()); 
                    }
                    pushFollow(FOLLOW_2);
                    ruleWhileStatement();

                    state._fsp--;
                    if (state.failed) return ;
                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getStatementAccess().getWhileStatementParserRuleCall_3()); 
                    }

                    }


                    }
                    break;
                case 5 :
                    // InternalMiniJava.g:1111:2: ( ruleForStatement )
                    {
                    // InternalMiniJava.g:1111:2: ( ruleForStatement )
                    // InternalMiniJava.g:1112:3: ruleForStatement
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getStatementAccess().getForStatementParserRuleCall_4()); 
                    }
                    pushFollow(FOLLOW_2);
                    ruleForStatement();

                    state._fsp--;
                    if (state.failed) return ;
                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getStatementAccess().getForStatementParserRuleCall_4()); 
                    }

                    }


                    }
                    break;
                case 6 :
                    // InternalMiniJava.g:1117:2: ( ( rule__Statement__Group_5__0 ) )
                    {
                    // InternalMiniJava.g:1117:2: ( ( rule__Statement__Group_5__0 ) )
                    // InternalMiniJava.g:1118:3: ( rule__Statement__Group_5__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getStatementAccess().getGroup_5()); 
                    }
                    // InternalMiniJava.g:1119:3: ( rule__Statement__Group_5__0 )
                    // InternalMiniJava.g:1119:4: rule__Statement__Group_5__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Statement__Group_5__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getStatementAccess().getGroup_5()); 
                    }

                    }


                    }
                    break;
                case 7 :
                    // InternalMiniJava.g:1123:2: ( ruleBlock )
                    {
                    // InternalMiniJava.g:1123:2: ( ruleBlock )
                    // InternalMiniJava.g:1124:3: ruleBlock
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getStatementAccess().getBlockParserRuleCall_6()); 
                    }
                    pushFollow(FOLLOW_2);
                    ruleBlock();

                    state._fsp--;
                    if (state.failed) return ;
                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getStatementAccess().getBlockParserRuleCall_6()); 
                    }

                    }


                    }
                    break;
                case 8 :
                    // InternalMiniJava.g:1129:2: ( ( rule__Statement__Group_7__0 ) )
                    {
                    // InternalMiniJava.g:1129:2: ( ( rule__Statement__Group_7__0 ) )
                    // InternalMiniJava.g:1130:3: ( rule__Statement__Group_7__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getStatementAccess().getGroup_7()); 
                    }
                    // InternalMiniJava.g:1131:3: ( rule__Statement__Group_7__0 )
                    // InternalMiniJava.g:1131:4: rule__Statement__Group_7__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Statement__Group_7__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getStatementAccess().getGroup_7()); 
                    }

                    }


                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Statement__Alternatives"


    // $ANTLR start "rule__SingleTypeRef__Alternatives"
    // InternalMiniJava.g:1139:1: rule__SingleTypeRef__Alternatives : ( ( ruleClassRef ) | ( ( rule__SingleTypeRef__Group_1__0 ) ) | ( ( rule__SingleTypeRef__Group_2__0 ) ) | ( ( rule__SingleTypeRef__Group_3__0 ) ) | ( ( rule__SingleTypeRef__Group_4__0 ) ) );
    public final void rule__SingleTypeRef__Alternatives() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1143:1: ( ( ruleClassRef ) | ( ( rule__SingleTypeRef__Group_1__0 ) ) | ( ( rule__SingleTypeRef__Group_2__0 ) ) | ( ( rule__SingleTypeRef__Group_3__0 ) ) | ( ( rule__SingleTypeRef__Group_4__0 ) ) )
            int alt5=5;
            switch ( input.LA(1) ) {
            case RULE_ID:
                {
                alt5=1;
                }
                break;
            case 41:
                {
                alt5=2;
                }
                break;
            case 42:
                {
                alt5=3;
                }
                break;
            case 43:
                {
                alt5=4;
                }
                break;
            case 44:
                {
                alt5=5;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return ;}
                NoViableAltException nvae =
                    new NoViableAltException("", 5, 0, input);

                throw nvae;
            }

            switch (alt5) {
                case 1 :
                    // InternalMiniJava.g:1144:2: ( ruleClassRef )
                    {
                    // InternalMiniJava.g:1144:2: ( ruleClassRef )
                    // InternalMiniJava.g:1145:3: ruleClassRef
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getSingleTypeRefAccess().getClassRefParserRuleCall_0()); 
                    }
                    pushFollow(FOLLOW_2);
                    ruleClassRef();

                    state._fsp--;
                    if (state.failed) return ;
                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getSingleTypeRefAccess().getClassRefParserRuleCall_0()); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalMiniJava.g:1150:2: ( ( rule__SingleTypeRef__Group_1__0 ) )
                    {
                    // InternalMiniJava.g:1150:2: ( ( rule__SingleTypeRef__Group_1__0 ) )
                    // InternalMiniJava.g:1151:3: ( rule__SingleTypeRef__Group_1__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getSingleTypeRefAccess().getGroup_1()); 
                    }
                    // InternalMiniJava.g:1152:3: ( rule__SingleTypeRef__Group_1__0 )
                    // InternalMiniJava.g:1152:4: rule__SingleTypeRef__Group_1__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__SingleTypeRef__Group_1__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getSingleTypeRefAccess().getGroup_1()); 
                    }

                    }


                    }
                    break;
                case 3 :
                    // InternalMiniJava.g:1156:2: ( ( rule__SingleTypeRef__Group_2__0 ) )
                    {
                    // InternalMiniJava.g:1156:2: ( ( rule__SingleTypeRef__Group_2__0 ) )
                    // InternalMiniJava.g:1157:3: ( rule__SingleTypeRef__Group_2__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getSingleTypeRefAccess().getGroup_2()); 
                    }
                    // InternalMiniJava.g:1158:3: ( rule__SingleTypeRef__Group_2__0 )
                    // InternalMiniJava.g:1158:4: rule__SingleTypeRef__Group_2__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__SingleTypeRef__Group_2__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getSingleTypeRefAccess().getGroup_2()); 
                    }

                    }


                    }
                    break;
                case 4 :
                    // InternalMiniJava.g:1162:2: ( ( rule__SingleTypeRef__Group_3__0 ) )
                    {
                    // InternalMiniJava.g:1162:2: ( ( rule__SingleTypeRef__Group_3__0 ) )
                    // InternalMiniJava.g:1163:3: ( rule__SingleTypeRef__Group_3__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getSingleTypeRefAccess().getGroup_3()); 
                    }
                    // InternalMiniJava.g:1164:3: ( rule__SingleTypeRef__Group_3__0 )
                    // InternalMiniJava.g:1164:4: rule__SingleTypeRef__Group_3__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__SingleTypeRef__Group_3__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getSingleTypeRefAccess().getGroup_3()); 
                    }

                    }


                    }
                    break;
                case 5 :
                    // InternalMiniJava.g:1168:2: ( ( rule__SingleTypeRef__Group_4__0 ) )
                    {
                    // InternalMiniJava.g:1168:2: ( ( rule__SingleTypeRef__Group_4__0 ) )
                    // InternalMiniJava.g:1169:3: ( rule__SingleTypeRef__Group_4__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getSingleTypeRefAccess().getGroup_4()); 
                    }
                    // InternalMiniJava.g:1170:3: ( rule__SingleTypeRef__Group_4__0 )
                    // InternalMiniJava.g:1170:4: rule__SingleTypeRef__Group_4__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__SingleTypeRef__Group_4__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getSingleTypeRefAccess().getGroup_4()); 
                    }

                    }


                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SingleTypeRef__Alternatives"


    // $ANTLR start "rule__TypedDeclaration__Alternatives"
    // InternalMiniJava.g:1178:1: rule__TypedDeclaration__Alternatives : ( ( ruleSymbol ) | ( ruleMember ) );
    public final void rule__TypedDeclaration__Alternatives() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1182:1: ( ( ruleSymbol ) | ( ruleMember ) )
            int alt6=2;
            alt6 = dfa6.predict(input);
            switch (alt6) {
                case 1 :
                    // InternalMiniJava.g:1183:2: ( ruleSymbol )
                    {
                    // InternalMiniJava.g:1183:2: ( ruleSymbol )
                    // InternalMiniJava.g:1184:3: ruleSymbol
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getTypedDeclarationAccess().getSymbolParserRuleCall_0()); 
                    }
                    pushFollow(FOLLOW_2);
                    ruleSymbol();

                    state._fsp--;
                    if (state.failed) return ;
                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getTypedDeclarationAccess().getSymbolParserRuleCall_0()); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalMiniJava.g:1189:2: ( ruleMember )
                    {
                    // InternalMiniJava.g:1189:2: ( ruleMember )
                    // InternalMiniJava.g:1190:3: ruleMember
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getTypedDeclarationAccess().getMemberParserRuleCall_1()); 
                    }
                    pushFollow(FOLLOW_2);
                    ruleMember();

                    state._fsp--;
                    if (state.failed) return ;
                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getTypedDeclarationAccess().getMemberParserRuleCall_1()); 
                    }

                    }


                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TypedDeclaration__Alternatives"


    // $ANTLR start "rule__Symbol__Alternatives"
    // InternalMiniJava.g:1199:1: rule__Symbol__Alternatives : ( ( ( ruleParameter ) ) | ( ruleVariableDeclaration ) );
    public final void rule__Symbol__Alternatives() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1203:1: ( ( ( ruleParameter ) ) | ( ruleVariableDeclaration ) )
            int alt7=2;
            alt7 = dfa7.predict(input);
            switch (alt7) {
                case 1 :
                    // InternalMiniJava.g:1204:2: ( ( ruleParameter ) )
                    {
                    // InternalMiniJava.g:1204:2: ( ( ruleParameter ) )
                    // InternalMiniJava.g:1205:3: ( ruleParameter )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getSymbolAccess().getParameterParserRuleCall_0()); 
                    }
                    // InternalMiniJava.g:1206:3: ( ruleParameter )
                    // InternalMiniJava.g:1206:4: ruleParameter
                    {
                    pushFollow(FOLLOW_2);
                    ruleParameter();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getSymbolAccess().getParameterParserRuleCall_0()); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalMiniJava.g:1210:2: ( ruleVariableDeclaration )
                    {
                    // InternalMiniJava.g:1210:2: ( ruleVariableDeclaration )
                    // InternalMiniJava.g:1211:3: ruleVariableDeclaration
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getSymbolAccess().getVariableDeclarationParserRuleCall_1()); 
                    }
                    pushFollow(FOLLOW_2);
                    ruleVariableDeclaration();

                    state._fsp--;
                    if (state.failed) return ;
                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getSymbolAccess().getVariableDeclarationParserRuleCall_1()); 
                    }

                    }


                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Symbol__Alternatives"


    // $ANTLR start "rule__Assignee__Alternatives"
    // InternalMiniJava.g:1220:1: rule__Assignee__Alternatives : ( ( ( ruleArrayAccess ) ) | ( ruleVariableDeclaration ) );
    public final void rule__Assignee__Alternatives() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1224:1: ( ( ( ruleArrayAccess ) ) | ( ruleVariableDeclaration ) )
            int alt8=2;
            alt8 = dfa8.predict(input);
            switch (alt8) {
                case 1 :
                    // InternalMiniJava.g:1225:2: ( ( ruleArrayAccess ) )
                    {
                    // InternalMiniJava.g:1225:2: ( ( ruleArrayAccess ) )
                    // InternalMiniJava.g:1226:3: ( ruleArrayAccess )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getAssigneeAccess().getArrayAccessParserRuleCall_0()); 
                    }
                    // InternalMiniJava.g:1227:3: ( ruleArrayAccess )
                    // InternalMiniJava.g:1227:4: ruleArrayAccess
                    {
                    pushFollow(FOLLOW_2);
                    ruleArrayAccess();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getAssigneeAccess().getArrayAccessParserRuleCall_0()); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalMiniJava.g:1231:2: ( ruleVariableDeclaration )
                    {
                    // InternalMiniJava.g:1231:2: ( ruleVariableDeclaration )
                    // InternalMiniJava.g:1232:3: ruleVariableDeclaration
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getAssigneeAccess().getVariableDeclarationParserRuleCall_1()); 
                    }
                    pushFollow(FOLLOW_2);
                    ruleVariableDeclaration();

                    state._fsp--;
                    if (state.failed) return ;
                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getAssigneeAccess().getVariableDeclarationParserRuleCall_1()); 
                    }

                    }


                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Assignee__Alternatives"


    // $ANTLR start "rule__Equality__Alternatives_1_0"
    // InternalMiniJava.g:1241:1: rule__Equality__Alternatives_1_0 : ( ( ( rule__Equality__Group_1_0_0__0 ) ) | ( ( rule__Equality__Group_1_0_1__0 ) ) );
    public final void rule__Equality__Alternatives_1_0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1245:1: ( ( ( rule__Equality__Group_1_0_0__0 ) ) | ( ( rule__Equality__Group_1_0_1__0 ) ) )
            int alt9=2;
            int LA9_0 = input.LA(1);

            if ( (LA9_0==47) ) {
                alt9=1;
            }
            else if ( (LA9_0==48) ) {
                alt9=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return ;}
                NoViableAltException nvae =
                    new NoViableAltException("", 9, 0, input);

                throw nvae;
            }
            switch (alt9) {
                case 1 :
                    // InternalMiniJava.g:1246:2: ( ( rule__Equality__Group_1_0_0__0 ) )
                    {
                    // InternalMiniJava.g:1246:2: ( ( rule__Equality__Group_1_0_0__0 ) )
                    // InternalMiniJava.g:1247:3: ( rule__Equality__Group_1_0_0__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getEqualityAccess().getGroup_1_0_0()); 
                    }
                    // InternalMiniJava.g:1248:3: ( rule__Equality__Group_1_0_0__0 )
                    // InternalMiniJava.g:1248:4: rule__Equality__Group_1_0_0__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Equality__Group_1_0_0__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getEqualityAccess().getGroup_1_0_0()); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalMiniJava.g:1252:2: ( ( rule__Equality__Group_1_0_1__0 ) )
                    {
                    // InternalMiniJava.g:1252:2: ( ( rule__Equality__Group_1_0_1__0 ) )
                    // InternalMiniJava.g:1253:3: ( rule__Equality__Group_1_0_1__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getEqualityAccess().getGroup_1_0_1()); 
                    }
                    // InternalMiniJava.g:1254:3: ( rule__Equality__Group_1_0_1__0 )
                    // InternalMiniJava.g:1254:4: rule__Equality__Group_1_0_1__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Equality__Group_1_0_1__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getEqualityAccess().getGroup_1_0_1()); 
                    }

                    }


                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Equality__Alternatives_1_0"


    // $ANTLR start "rule__Comparison__Alternatives_1_0"
    // InternalMiniJava.g:1262:1: rule__Comparison__Alternatives_1_0 : ( ( ( rule__Comparison__Group_1_0_0__0 ) ) | ( ( rule__Comparison__Group_1_0_1__0 ) ) | ( ( rule__Comparison__Group_1_0_2__0 ) ) | ( ( rule__Comparison__Group_1_0_3__0 ) ) );
    public final void rule__Comparison__Alternatives_1_0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1266:1: ( ( ( rule__Comparison__Group_1_0_0__0 ) ) | ( ( rule__Comparison__Group_1_0_1__0 ) ) | ( ( rule__Comparison__Group_1_0_2__0 ) ) | ( ( rule__Comparison__Group_1_0_3__0 ) ) )
            int alt10=4;
            switch ( input.LA(1) ) {
            case 49:
                {
                alt10=1;
                }
                break;
            case 50:
                {
                alt10=2;
                }
                break;
            case 51:
                {
                alt10=3;
                }
                break;
            case 52:
                {
                alt10=4;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return ;}
                NoViableAltException nvae =
                    new NoViableAltException("", 10, 0, input);

                throw nvae;
            }

            switch (alt10) {
                case 1 :
                    // InternalMiniJava.g:1267:2: ( ( rule__Comparison__Group_1_0_0__0 ) )
                    {
                    // InternalMiniJava.g:1267:2: ( ( rule__Comparison__Group_1_0_0__0 ) )
                    // InternalMiniJava.g:1268:3: ( rule__Comparison__Group_1_0_0__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getComparisonAccess().getGroup_1_0_0()); 
                    }
                    // InternalMiniJava.g:1269:3: ( rule__Comparison__Group_1_0_0__0 )
                    // InternalMiniJava.g:1269:4: rule__Comparison__Group_1_0_0__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Comparison__Group_1_0_0__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getComparisonAccess().getGroup_1_0_0()); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalMiniJava.g:1273:2: ( ( rule__Comparison__Group_1_0_1__0 ) )
                    {
                    // InternalMiniJava.g:1273:2: ( ( rule__Comparison__Group_1_0_1__0 ) )
                    // InternalMiniJava.g:1274:3: ( rule__Comparison__Group_1_0_1__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getComparisonAccess().getGroup_1_0_1()); 
                    }
                    // InternalMiniJava.g:1275:3: ( rule__Comparison__Group_1_0_1__0 )
                    // InternalMiniJava.g:1275:4: rule__Comparison__Group_1_0_1__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Comparison__Group_1_0_1__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getComparisonAccess().getGroup_1_0_1()); 
                    }

                    }


                    }
                    break;
                case 3 :
                    // InternalMiniJava.g:1279:2: ( ( rule__Comparison__Group_1_0_2__0 ) )
                    {
                    // InternalMiniJava.g:1279:2: ( ( rule__Comparison__Group_1_0_2__0 ) )
                    // InternalMiniJava.g:1280:3: ( rule__Comparison__Group_1_0_2__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getComparisonAccess().getGroup_1_0_2()); 
                    }
                    // InternalMiniJava.g:1281:3: ( rule__Comparison__Group_1_0_2__0 )
                    // InternalMiniJava.g:1281:4: rule__Comparison__Group_1_0_2__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Comparison__Group_1_0_2__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getComparisonAccess().getGroup_1_0_2()); 
                    }

                    }


                    }
                    break;
                case 4 :
                    // InternalMiniJava.g:1285:2: ( ( rule__Comparison__Group_1_0_3__0 ) )
                    {
                    // InternalMiniJava.g:1285:2: ( ( rule__Comparison__Group_1_0_3__0 ) )
                    // InternalMiniJava.g:1286:3: ( rule__Comparison__Group_1_0_3__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getComparisonAccess().getGroup_1_0_3()); 
                    }
                    // InternalMiniJava.g:1287:3: ( rule__Comparison__Group_1_0_3__0 )
                    // InternalMiniJava.g:1287:4: rule__Comparison__Group_1_0_3__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Comparison__Group_1_0_3__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getComparisonAccess().getGroup_1_0_3()); 
                    }

                    }


                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Alternatives_1_0"


    // $ANTLR start "rule__PlusOrMinus__Alternatives_1_0"
    // InternalMiniJava.g:1295:1: rule__PlusOrMinus__Alternatives_1_0 : ( ( ( rule__PlusOrMinus__Group_1_0_0__0 ) ) | ( ( rule__PlusOrMinus__Group_1_0_1__0 ) ) );
    public final void rule__PlusOrMinus__Alternatives_1_0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1299:1: ( ( ( rule__PlusOrMinus__Group_1_0_0__0 ) ) | ( ( rule__PlusOrMinus__Group_1_0_1__0 ) ) )
            int alt11=2;
            int LA11_0 = input.LA(1);

            if ( (LA11_0==53) ) {
                alt11=1;
            }
            else if ( (LA11_0==54) ) {
                alt11=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return ;}
                NoViableAltException nvae =
                    new NoViableAltException("", 11, 0, input);

                throw nvae;
            }
            switch (alt11) {
                case 1 :
                    // InternalMiniJava.g:1300:2: ( ( rule__PlusOrMinus__Group_1_0_0__0 ) )
                    {
                    // InternalMiniJava.g:1300:2: ( ( rule__PlusOrMinus__Group_1_0_0__0 ) )
                    // InternalMiniJava.g:1301:3: ( rule__PlusOrMinus__Group_1_0_0__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getPlusOrMinusAccess().getGroup_1_0_0()); 
                    }
                    // InternalMiniJava.g:1302:3: ( rule__PlusOrMinus__Group_1_0_0__0 )
                    // InternalMiniJava.g:1302:4: rule__PlusOrMinus__Group_1_0_0__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__PlusOrMinus__Group_1_0_0__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getPlusOrMinusAccess().getGroup_1_0_0()); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalMiniJava.g:1306:2: ( ( rule__PlusOrMinus__Group_1_0_1__0 ) )
                    {
                    // InternalMiniJava.g:1306:2: ( ( rule__PlusOrMinus__Group_1_0_1__0 ) )
                    // InternalMiniJava.g:1307:3: ( rule__PlusOrMinus__Group_1_0_1__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getPlusOrMinusAccess().getGroup_1_0_1()); 
                    }
                    // InternalMiniJava.g:1308:3: ( rule__PlusOrMinus__Group_1_0_1__0 )
                    // InternalMiniJava.g:1308:4: rule__PlusOrMinus__Group_1_0_1__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__PlusOrMinus__Group_1_0_1__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getPlusOrMinusAccess().getGroup_1_0_1()); 
                    }

                    }


                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PlusOrMinus__Alternatives_1_0"


    // $ANTLR start "rule__MulOrDiv__Alternatives_1_0"
    // InternalMiniJava.g:1316:1: rule__MulOrDiv__Alternatives_1_0 : ( ( ( rule__MulOrDiv__Group_1_0_0__0 ) ) | ( ( rule__MulOrDiv__Group_1_0_1__0 ) ) );
    public final void rule__MulOrDiv__Alternatives_1_0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1320:1: ( ( ( rule__MulOrDiv__Group_1_0_0__0 ) ) | ( ( rule__MulOrDiv__Group_1_0_1__0 ) ) )
            int alt12=2;
            int LA12_0 = input.LA(1);

            if ( (LA12_0==55) ) {
                alt12=1;
            }
            else if ( (LA12_0==56) ) {
                alt12=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return ;}
                NoViableAltException nvae =
                    new NoViableAltException("", 12, 0, input);

                throw nvae;
            }
            switch (alt12) {
                case 1 :
                    // InternalMiniJava.g:1321:2: ( ( rule__MulOrDiv__Group_1_0_0__0 ) )
                    {
                    // InternalMiniJava.g:1321:2: ( ( rule__MulOrDiv__Group_1_0_0__0 ) )
                    // InternalMiniJava.g:1322:3: ( rule__MulOrDiv__Group_1_0_0__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getMulOrDivAccess().getGroup_1_0_0()); 
                    }
                    // InternalMiniJava.g:1323:3: ( rule__MulOrDiv__Group_1_0_0__0 )
                    // InternalMiniJava.g:1323:4: rule__MulOrDiv__Group_1_0_0__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__MulOrDiv__Group_1_0_0__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getMulOrDivAccess().getGroup_1_0_0()); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalMiniJava.g:1327:2: ( ( rule__MulOrDiv__Group_1_0_1__0 ) )
                    {
                    // InternalMiniJava.g:1327:2: ( ( rule__MulOrDiv__Group_1_0_1__0 ) )
                    // InternalMiniJava.g:1328:3: ( rule__MulOrDiv__Group_1_0_1__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getMulOrDivAccess().getGroup_1_0_1()); 
                    }
                    // InternalMiniJava.g:1329:3: ( rule__MulOrDiv__Group_1_0_1__0 )
                    // InternalMiniJava.g:1329:4: rule__MulOrDiv__Group_1_0_1__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__MulOrDiv__Group_1_0_1__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getMulOrDivAccess().getGroup_1_0_1()); 
                    }

                    }


                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__MulOrDiv__Alternatives_1_0"


    // $ANTLR start "rule__Primary__Alternatives"
    // InternalMiniJava.g:1337:1: rule__Primary__Alternatives : ( ( ( rule__Primary__Group_0__0 ) ) | ( ( rule__Primary__Group_1__0 ) ) | ( ( rule__Primary__Group_2__0 ) ) | ( ruleSelectionExpression ) );
    public final void rule__Primary__Alternatives() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1341:1: ( ( ( rule__Primary__Group_0__0 ) ) | ( ( rule__Primary__Group_1__0 ) ) | ( ( rule__Primary__Group_2__0 ) ) | ( ruleSelectionExpression ) )
            int alt13=4;
            switch ( input.LA(1) ) {
            case 28:
                {
                alt13=1;
                }
                break;
            case 58:
                {
                alt13=2;
                }
                break;
            case 54:
                {
                alt13=3;
                }
                break;
            case RULE_ID:
            case RULE_STRING:
            case RULE_INT:
            case 12:
            case 13:
            case 59:
            case 60:
            case 61:
            case 62:
                {
                alt13=4;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return ;}
                NoViableAltException nvae =
                    new NoViableAltException("", 13, 0, input);

                throw nvae;
            }

            switch (alt13) {
                case 1 :
                    // InternalMiniJava.g:1342:2: ( ( rule__Primary__Group_0__0 ) )
                    {
                    // InternalMiniJava.g:1342:2: ( ( rule__Primary__Group_0__0 ) )
                    // InternalMiniJava.g:1343:3: ( rule__Primary__Group_0__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getPrimaryAccess().getGroup_0()); 
                    }
                    // InternalMiniJava.g:1344:3: ( rule__Primary__Group_0__0 )
                    // InternalMiniJava.g:1344:4: rule__Primary__Group_0__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Primary__Group_0__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getPrimaryAccess().getGroup_0()); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalMiniJava.g:1348:2: ( ( rule__Primary__Group_1__0 ) )
                    {
                    // InternalMiniJava.g:1348:2: ( ( rule__Primary__Group_1__0 ) )
                    // InternalMiniJava.g:1349:3: ( rule__Primary__Group_1__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getPrimaryAccess().getGroup_1()); 
                    }
                    // InternalMiniJava.g:1350:3: ( rule__Primary__Group_1__0 )
                    // InternalMiniJava.g:1350:4: rule__Primary__Group_1__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Primary__Group_1__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getPrimaryAccess().getGroup_1()); 
                    }

                    }


                    }
                    break;
                case 3 :
                    // InternalMiniJava.g:1354:2: ( ( rule__Primary__Group_2__0 ) )
                    {
                    // InternalMiniJava.g:1354:2: ( ( rule__Primary__Group_2__0 ) )
                    // InternalMiniJava.g:1355:3: ( rule__Primary__Group_2__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getPrimaryAccess().getGroup_2()); 
                    }
                    // InternalMiniJava.g:1356:3: ( rule__Primary__Group_2__0 )
                    // InternalMiniJava.g:1356:4: rule__Primary__Group_2__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Primary__Group_2__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getPrimaryAccess().getGroup_2()); 
                    }

                    }


                    }
                    break;
                case 4 :
                    // InternalMiniJava.g:1360:2: ( ruleSelectionExpression )
                    {
                    // InternalMiniJava.g:1360:2: ( ruleSelectionExpression )
                    // InternalMiniJava.g:1361:3: ruleSelectionExpression
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getPrimaryAccess().getSelectionExpressionParserRuleCall_3()); 
                    }
                    pushFollow(FOLLOW_2);
                    ruleSelectionExpression();

                    state._fsp--;
                    if (state.failed) return ;
                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getPrimaryAccess().getSelectionExpressionParserRuleCall_3()); 
                    }

                    }


                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Primary__Alternatives"


    // $ANTLR start "rule__SelectionExpression__Alternatives_1"
    // InternalMiniJava.g:1370:1: rule__SelectionExpression__Alternatives_1 : ( ( ( rule__SelectionExpression__Group_1_0__0 ) ) | ( ( rule__SelectionExpression__Group_1_1__0 ) ) );
    public final void rule__SelectionExpression__Alternatives_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1374:1: ( ( ( rule__SelectionExpression__Group_1_0__0 ) ) | ( ( rule__SelectionExpression__Group_1_1__0 ) ) )
            int alt14=2;
            int LA14_0 = input.LA(1);

            if ( (LA14_0==19) ) {
                int LA14_1 = input.LA(2);

                if ( (LA14_1==RULE_ID) ) {
                    int LA14_2 = input.LA(3);

                    if ( (LA14_2==EOF||LA14_2==11||LA14_2==19||LA14_2==26||(LA14_2>=29 && LA14_2<=30)||(LA14_2>=39 && LA14_2<=40)||(LA14_2>=45 && LA14_2<=56)) ) {
                        alt14=1;
                    }
                    else if ( (LA14_2==28) ) {
                        alt14=2;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return ;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 14, 2, input);

                        throw nvae;
                    }
                }
                else {
                    if (state.backtracking>0) {state.failed=true; return ;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 14, 1, input);

                    throw nvae;
                }
            }
            else {
                if (state.backtracking>0) {state.failed=true; return ;}
                NoViableAltException nvae =
                    new NoViableAltException("", 14, 0, input);

                throw nvae;
            }
            switch (alt14) {
                case 1 :
                    // InternalMiniJava.g:1375:2: ( ( rule__SelectionExpression__Group_1_0__0 ) )
                    {
                    // InternalMiniJava.g:1375:2: ( ( rule__SelectionExpression__Group_1_0__0 ) )
                    // InternalMiniJava.g:1376:3: ( rule__SelectionExpression__Group_1_0__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getSelectionExpressionAccess().getGroup_1_0()); 
                    }
                    // InternalMiniJava.g:1377:3: ( rule__SelectionExpression__Group_1_0__0 )
                    // InternalMiniJava.g:1377:4: rule__SelectionExpression__Group_1_0__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__SelectionExpression__Group_1_0__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getSelectionExpressionAccess().getGroup_1_0()); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalMiniJava.g:1381:2: ( ( rule__SelectionExpression__Group_1_1__0 ) )
                    {
                    // InternalMiniJava.g:1381:2: ( ( rule__SelectionExpression__Group_1_1__0 ) )
                    // InternalMiniJava.g:1382:3: ( rule__SelectionExpression__Group_1_1__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getSelectionExpressionAccess().getGroup_1_1()); 
                    }
                    // InternalMiniJava.g:1383:3: ( rule__SelectionExpression__Group_1_1__0 )
                    // InternalMiniJava.g:1383:4: rule__SelectionExpression__Group_1_1__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__SelectionExpression__Group_1_1__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getSelectionExpressionAccess().getGroup_1_1()); 
                    }

                    }


                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Alternatives_1"


    // $ANTLR start "rule__TerminalExpression__Alternatives"
    // InternalMiniJava.g:1391:1: rule__TerminalExpression__Alternatives : ( ( ( rule__TerminalExpression__Group_0__0 ) ) | ( ( rule__TerminalExpression__Group_1__0 ) ) | ( ( rule__TerminalExpression__Group_2__0 ) ) | ( ( rule__TerminalExpression__Group_3__0 ) ) | ( ( rule__TerminalExpression__Group_4__0 ) ) | ( ( rule__TerminalExpression__Group_5__0 ) ) | ( ( rule__TerminalExpression__Group_6__0 ) ) | ( ( rule__TerminalExpression__Group_7__0 ) ) | ( ( rule__TerminalExpression__Group_8__0 ) ) );
    public final void rule__TerminalExpression__Alternatives() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1395:1: ( ( ( rule__TerminalExpression__Group_0__0 ) ) | ( ( rule__TerminalExpression__Group_1__0 ) ) | ( ( rule__TerminalExpression__Group_2__0 ) ) | ( ( rule__TerminalExpression__Group_3__0 ) ) | ( ( rule__TerminalExpression__Group_4__0 ) ) | ( ( rule__TerminalExpression__Group_5__0 ) ) | ( ( rule__TerminalExpression__Group_6__0 ) ) | ( ( rule__TerminalExpression__Group_7__0 ) ) | ( ( rule__TerminalExpression__Group_8__0 ) ) )
            int alt15=9;
            alt15 = dfa15.predict(input);
            switch (alt15) {
                case 1 :
                    // InternalMiniJava.g:1396:2: ( ( rule__TerminalExpression__Group_0__0 ) )
                    {
                    // InternalMiniJava.g:1396:2: ( ( rule__TerminalExpression__Group_0__0 ) )
                    // InternalMiniJava.g:1397:3: ( rule__TerminalExpression__Group_0__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getTerminalExpressionAccess().getGroup_0()); 
                    }
                    // InternalMiniJava.g:1398:3: ( rule__TerminalExpression__Group_0__0 )
                    // InternalMiniJava.g:1398:4: rule__TerminalExpression__Group_0__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__TerminalExpression__Group_0__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getTerminalExpressionAccess().getGroup_0()); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalMiniJava.g:1402:2: ( ( rule__TerminalExpression__Group_1__0 ) )
                    {
                    // InternalMiniJava.g:1402:2: ( ( rule__TerminalExpression__Group_1__0 ) )
                    // InternalMiniJava.g:1403:3: ( rule__TerminalExpression__Group_1__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getTerminalExpressionAccess().getGroup_1()); 
                    }
                    // InternalMiniJava.g:1404:3: ( rule__TerminalExpression__Group_1__0 )
                    // InternalMiniJava.g:1404:4: rule__TerminalExpression__Group_1__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__TerminalExpression__Group_1__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getTerminalExpressionAccess().getGroup_1()); 
                    }

                    }


                    }
                    break;
                case 3 :
                    // InternalMiniJava.g:1408:2: ( ( rule__TerminalExpression__Group_2__0 ) )
                    {
                    // InternalMiniJava.g:1408:2: ( ( rule__TerminalExpression__Group_2__0 ) )
                    // InternalMiniJava.g:1409:3: ( rule__TerminalExpression__Group_2__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getTerminalExpressionAccess().getGroup_2()); 
                    }
                    // InternalMiniJava.g:1410:3: ( rule__TerminalExpression__Group_2__0 )
                    // InternalMiniJava.g:1410:4: rule__TerminalExpression__Group_2__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__TerminalExpression__Group_2__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getTerminalExpressionAccess().getGroup_2()); 
                    }

                    }


                    }
                    break;
                case 4 :
                    // InternalMiniJava.g:1414:2: ( ( rule__TerminalExpression__Group_3__0 ) )
                    {
                    // InternalMiniJava.g:1414:2: ( ( rule__TerminalExpression__Group_3__0 ) )
                    // InternalMiniJava.g:1415:3: ( rule__TerminalExpression__Group_3__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getTerminalExpressionAccess().getGroup_3()); 
                    }
                    // InternalMiniJava.g:1416:3: ( rule__TerminalExpression__Group_3__0 )
                    // InternalMiniJava.g:1416:4: rule__TerminalExpression__Group_3__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__TerminalExpression__Group_3__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getTerminalExpressionAccess().getGroup_3()); 
                    }

                    }


                    }
                    break;
                case 5 :
                    // InternalMiniJava.g:1420:2: ( ( rule__TerminalExpression__Group_4__0 ) )
                    {
                    // InternalMiniJava.g:1420:2: ( ( rule__TerminalExpression__Group_4__0 ) )
                    // InternalMiniJava.g:1421:3: ( rule__TerminalExpression__Group_4__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getTerminalExpressionAccess().getGroup_4()); 
                    }
                    // InternalMiniJava.g:1422:3: ( rule__TerminalExpression__Group_4__0 )
                    // InternalMiniJava.g:1422:4: rule__TerminalExpression__Group_4__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__TerminalExpression__Group_4__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getTerminalExpressionAccess().getGroup_4()); 
                    }

                    }


                    }
                    break;
                case 6 :
                    // InternalMiniJava.g:1426:2: ( ( rule__TerminalExpression__Group_5__0 ) )
                    {
                    // InternalMiniJava.g:1426:2: ( ( rule__TerminalExpression__Group_5__0 ) )
                    // InternalMiniJava.g:1427:3: ( rule__TerminalExpression__Group_5__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getTerminalExpressionAccess().getGroup_5()); 
                    }
                    // InternalMiniJava.g:1428:3: ( rule__TerminalExpression__Group_5__0 )
                    // InternalMiniJava.g:1428:4: rule__TerminalExpression__Group_5__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__TerminalExpression__Group_5__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getTerminalExpressionAccess().getGroup_5()); 
                    }

                    }


                    }
                    break;
                case 7 :
                    // InternalMiniJava.g:1432:2: ( ( rule__TerminalExpression__Group_6__0 ) )
                    {
                    // InternalMiniJava.g:1432:2: ( ( rule__TerminalExpression__Group_6__0 ) )
                    // InternalMiniJava.g:1433:3: ( rule__TerminalExpression__Group_6__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getTerminalExpressionAccess().getGroup_6()); 
                    }
                    // InternalMiniJava.g:1434:3: ( rule__TerminalExpression__Group_6__0 )
                    // InternalMiniJava.g:1434:4: rule__TerminalExpression__Group_6__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__TerminalExpression__Group_6__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getTerminalExpressionAccess().getGroup_6()); 
                    }

                    }


                    }
                    break;
                case 8 :
                    // InternalMiniJava.g:1438:2: ( ( rule__TerminalExpression__Group_7__0 ) )
                    {
                    // InternalMiniJava.g:1438:2: ( ( rule__TerminalExpression__Group_7__0 ) )
                    // InternalMiniJava.g:1439:3: ( rule__TerminalExpression__Group_7__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getTerminalExpressionAccess().getGroup_7()); 
                    }
                    // InternalMiniJava.g:1440:3: ( rule__TerminalExpression__Group_7__0 )
                    // InternalMiniJava.g:1440:4: rule__TerminalExpression__Group_7__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__TerminalExpression__Group_7__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getTerminalExpressionAccess().getGroup_7()); 
                    }

                    }


                    }
                    break;
                case 9 :
                    // InternalMiniJava.g:1444:2: ( ( rule__TerminalExpression__Group_8__0 ) )
                    {
                    // InternalMiniJava.g:1444:2: ( ( rule__TerminalExpression__Group_8__0 ) )
                    // InternalMiniJava.g:1445:3: ( rule__TerminalExpression__Group_8__0 )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getTerminalExpressionAccess().getGroup_8()); 
                    }
                    // InternalMiniJava.g:1446:3: ( rule__TerminalExpression__Group_8__0 )
                    // InternalMiniJava.g:1446:4: rule__TerminalExpression__Group_8__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__TerminalExpression__Group_8__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getTerminalExpressionAccess().getGroup_8()); 
                    }

                    }


                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Alternatives"


    // $ANTLR start "rule__TerminalExpression__ValueAlternatives_2_1_0"
    // InternalMiniJava.g:1454:1: rule__TerminalExpression__ValueAlternatives_2_1_0 : ( ( 'true' ) | ( 'false' ) );
    public final void rule__TerminalExpression__ValueAlternatives_2_1_0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1458:1: ( ( 'true' ) | ( 'false' ) )
            int alt16=2;
            int LA16_0 = input.LA(1);

            if ( (LA16_0==12) ) {
                alt16=1;
            }
            else if ( (LA16_0==13) ) {
                alt16=2;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return ;}
                NoViableAltException nvae =
                    new NoViableAltException("", 16, 0, input);

                throw nvae;
            }
            switch (alt16) {
                case 1 :
                    // InternalMiniJava.g:1459:2: ( 'true' )
                    {
                    // InternalMiniJava.g:1459:2: ( 'true' )
                    // InternalMiniJava.g:1460:3: 'true'
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getTerminalExpressionAccess().getValueTrueKeyword_2_1_0_0()); 
                    }
                    match(input,12,FOLLOW_2); if (state.failed) return ;
                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getTerminalExpressionAccess().getValueTrueKeyword_2_1_0_0()); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalMiniJava.g:1465:2: ( 'false' )
                    {
                    // InternalMiniJava.g:1465:2: ( 'false' )
                    // InternalMiniJava.g:1466:3: 'false'
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getTerminalExpressionAccess().getValueFalseKeyword_2_1_0_1()); 
                    }
                    match(input,13,FOLLOW_2); if (state.failed) return ;
                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getTerminalExpressionAccess().getValueFalseKeyword_2_1_0_1()); 
                    }

                    }


                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__ValueAlternatives_2_1_0"


    // $ANTLR start "rule__AccessLevel__Alternatives"
    // InternalMiniJava.g:1475:1: rule__AccessLevel__Alternatives : ( ( ( 'private' ) ) | ( ( 'protected' ) ) | ( ( 'public' ) ) );
    public final void rule__AccessLevel__Alternatives() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1479:1: ( ( ( 'private' ) ) | ( ( 'protected' ) ) | ( ( 'public' ) ) )
            int alt17=3;
            switch ( input.LA(1) ) {
            case 14:
                {
                alt17=1;
                }
                break;
            case 15:
                {
                alt17=2;
                }
                break;
            case 16:
                {
                alt17=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return ;}
                NoViableAltException nvae =
                    new NoViableAltException("", 17, 0, input);

                throw nvae;
            }

            switch (alt17) {
                case 1 :
                    // InternalMiniJava.g:1480:2: ( ( 'private' ) )
                    {
                    // InternalMiniJava.g:1480:2: ( ( 'private' ) )
                    // InternalMiniJava.g:1481:3: ( 'private' )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getAccessLevelAccess().getPRIVATEEnumLiteralDeclaration_0()); 
                    }
                    // InternalMiniJava.g:1482:3: ( 'private' )
                    // InternalMiniJava.g:1482:4: 'private'
                    {
                    match(input,14,FOLLOW_2); if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getAccessLevelAccess().getPRIVATEEnumLiteralDeclaration_0()); 
                    }

                    }


                    }
                    break;
                case 2 :
                    // InternalMiniJava.g:1486:2: ( ( 'protected' ) )
                    {
                    // InternalMiniJava.g:1486:2: ( ( 'protected' ) )
                    // InternalMiniJava.g:1487:3: ( 'protected' )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getAccessLevelAccess().getPROTECTEDEnumLiteralDeclaration_1()); 
                    }
                    // InternalMiniJava.g:1488:3: ( 'protected' )
                    // InternalMiniJava.g:1488:4: 'protected'
                    {
                    match(input,15,FOLLOW_2); if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getAccessLevelAccess().getPROTECTEDEnumLiteralDeclaration_1()); 
                    }

                    }


                    }
                    break;
                case 3 :
                    // InternalMiniJava.g:1492:2: ( ( 'public' ) )
                    {
                    // InternalMiniJava.g:1492:2: ( ( 'public' ) )
                    // InternalMiniJava.g:1493:3: ( 'public' )
                    {
                    if ( state.backtracking==0 ) {
                       before(grammarAccess.getAccessLevelAccess().getPUBLICEnumLiteralDeclaration_2()); 
                    }
                    // InternalMiniJava.g:1494:3: ( 'public' )
                    // InternalMiniJava.g:1494:4: 'public'
                    {
                    match(input,16,FOLLOW_2); if (state.failed) return ;

                    }

                    if ( state.backtracking==0 ) {
                       after(grammarAccess.getAccessLevelAccess().getPUBLICEnumLiteralDeclaration_2()); 
                    }

                    }


                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__AccessLevel__Alternatives"


    // $ANTLR start "rule__Program__Group__0"
    // InternalMiniJava.g:1502:1: rule__Program__Group__0 : rule__Program__Group__0__Impl rule__Program__Group__1 ;
    public final void rule__Program__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1506:1: ( rule__Program__Group__0__Impl rule__Program__Group__1 )
            // InternalMiniJava.g:1507:2: rule__Program__Group__0__Impl rule__Program__Group__1
            {
            pushFollow(FOLLOW_3);
            rule__Program__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Program__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Program__Group__0"


    // $ANTLR start "rule__Program__Group__0__Impl"
    // InternalMiniJava.g:1514:1: rule__Program__Group__0__Impl : ( ( rule__Program__Group_0__0 )? ) ;
    public final void rule__Program__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1518:1: ( ( ( rule__Program__Group_0__0 )? ) )
            // InternalMiniJava.g:1519:1: ( ( rule__Program__Group_0__0 )? )
            {
            // InternalMiniJava.g:1519:1: ( ( rule__Program__Group_0__0 )? )
            // InternalMiniJava.g:1520:2: ( rule__Program__Group_0__0 )?
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getProgramAccess().getGroup_0()); 
            }
            // InternalMiniJava.g:1521:2: ( rule__Program__Group_0__0 )?
            int alt18=2;
            int LA18_0 = input.LA(1);

            if ( (LA18_0==17) ) {
                alt18=1;
            }
            switch (alt18) {
                case 1 :
                    // InternalMiniJava.g:1521:3: rule__Program__Group_0__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Program__Group_0__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getProgramAccess().getGroup_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Program__Group__0__Impl"


    // $ANTLR start "rule__Program__Group__1"
    // InternalMiniJava.g:1529:1: rule__Program__Group__1 : rule__Program__Group__1__Impl rule__Program__Group__2 ;
    public final void rule__Program__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1533:1: ( rule__Program__Group__1__Impl rule__Program__Group__2 )
            // InternalMiniJava.g:1534:2: rule__Program__Group__1__Impl rule__Program__Group__2
            {
            pushFollow(FOLLOW_3);
            rule__Program__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Program__Group__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Program__Group__1"


    // $ANTLR start "rule__Program__Group__1__Impl"
    // InternalMiniJava.g:1541:1: rule__Program__Group__1__Impl : ( ( rule__Program__ImportsAssignment_1 )* ) ;
    public final void rule__Program__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1545:1: ( ( ( rule__Program__ImportsAssignment_1 )* ) )
            // InternalMiniJava.g:1546:1: ( ( rule__Program__ImportsAssignment_1 )* )
            {
            // InternalMiniJava.g:1546:1: ( ( rule__Program__ImportsAssignment_1 )* )
            // InternalMiniJava.g:1547:2: ( rule__Program__ImportsAssignment_1 )*
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getProgramAccess().getImportsAssignment_1()); 
            }
            // InternalMiniJava.g:1548:2: ( rule__Program__ImportsAssignment_1 )*
            loop19:
            do {
                int alt19=2;
                int LA19_0 = input.LA(1);

                if ( (LA19_0==18) ) {
                    alt19=1;
                }


                switch (alt19) {
            	case 1 :
            	    // InternalMiniJava.g:1548:3: rule__Program__ImportsAssignment_1
            	    {
            	    pushFollow(FOLLOW_4);
            	    rule__Program__ImportsAssignment_1();

            	    state._fsp--;
            	    if (state.failed) return ;

            	    }
            	    break;

            	default :
            	    break loop19;
                }
            } while (true);

            if ( state.backtracking==0 ) {
               after(grammarAccess.getProgramAccess().getImportsAssignment_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Program__Group__1__Impl"


    // $ANTLR start "rule__Program__Group__2"
    // InternalMiniJava.g:1556:1: rule__Program__Group__2 : rule__Program__Group__2__Impl ;
    public final void rule__Program__Group__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1560:1: ( rule__Program__Group__2__Impl )
            // InternalMiniJava.g:1561:2: rule__Program__Group__2__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Program__Group__2__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Program__Group__2"


    // $ANTLR start "rule__Program__Group__2__Impl"
    // InternalMiniJava.g:1567:1: rule__Program__Group__2__Impl : ( ( rule__Program__ClassesAssignment_2 )* ) ;
    public final void rule__Program__Group__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1571:1: ( ( ( rule__Program__ClassesAssignment_2 )* ) )
            // InternalMiniJava.g:1572:1: ( ( rule__Program__ClassesAssignment_2 )* )
            {
            // InternalMiniJava.g:1572:1: ( ( rule__Program__ClassesAssignment_2 )* )
            // InternalMiniJava.g:1573:2: ( rule__Program__ClassesAssignment_2 )*
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getProgramAccess().getClassesAssignment_2()); 
            }
            // InternalMiniJava.g:1574:2: ( rule__Program__ClassesAssignment_2 )*
            loop20:
            do {
                int alt20=2;
                int LA20_0 = input.LA(1);

                if ( ((LA20_0>=14 && LA20_0<=16)||LA20_0==21||LA20_0==27||LA20_0==63) ) {
                    alt20=1;
                }


                switch (alt20) {
            	case 1 :
            	    // InternalMiniJava.g:1574:3: rule__Program__ClassesAssignment_2
            	    {
            	    pushFollow(FOLLOW_5);
            	    rule__Program__ClassesAssignment_2();

            	    state._fsp--;
            	    if (state.failed) return ;

            	    }
            	    break;

            	default :
            	    break loop20;
                }
            } while (true);

            if ( state.backtracking==0 ) {
               after(grammarAccess.getProgramAccess().getClassesAssignment_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Program__Group__2__Impl"


    // $ANTLR start "rule__Program__Group_0__0"
    // InternalMiniJava.g:1583:1: rule__Program__Group_0__0 : rule__Program__Group_0__0__Impl rule__Program__Group_0__1 ;
    public final void rule__Program__Group_0__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1587:1: ( rule__Program__Group_0__0__Impl rule__Program__Group_0__1 )
            // InternalMiniJava.g:1588:2: rule__Program__Group_0__0__Impl rule__Program__Group_0__1
            {
            pushFollow(FOLLOW_6);
            rule__Program__Group_0__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Program__Group_0__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Program__Group_0__0"


    // $ANTLR start "rule__Program__Group_0__0__Impl"
    // InternalMiniJava.g:1595:1: rule__Program__Group_0__0__Impl : ( 'package' ) ;
    public final void rule__Program__Group_0__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1599:1: ( ( 'package' ) )
            // InternalMiniJava.g:1600:1: ( 'package' )
            {
            // InternalMiniJava.g:1600:1: ( 'package' )
            // InternalMiniJava.g:1601:2: 'package'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getProgramAccess().getPackageKeyword_0_0()); 
            }
            match(input,17,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getProgramAccess().getPackageKeyword_0_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Program__Group_0__0__Impl"


    // $ANTLR start "rule__Program__Group_0__1"
    // InternalMiniJava.g:1610:1: rule__Program__Group_0__1 : rule__Program__Group_0__1__Impl rule__Program__Group_0__2 ;
    public final void rule__Program__Group_0__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1614:1: ( rule__Program__Group_0__1__Impl rule__Program__Group_0__2 )
            // InternalMiniJava.g:1615:2: rule__Program__Group_0__1__Impl rule__Program__Group_0__2
            {
            pushFollow(FOLLOW_7);
            rule__Program__Group_0__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Program__Group_0__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Program__Group_0__1"


    // $ANTLR start "rule__Program__Group_0__1__Impl"
    // InternalMiniJava.g:1622:1: rule__Program__Group_0__1__Impl : ( ( rule__Program__NameAssignment_0_1 ) ) ;
    public final void rule__Program__Group_0__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1626:1: ( ( ( rule__Program__NameAssignment_0_1 ) ) )
            // InternalMiniJava.g:1627:1: ( ( rule__Program__NameAssignment_0_1 ) )
            {
            // InternalMiniJava.g:1627:1: ( ( rule__Program__NameAssignment_0_1 ) )
            // InternalMiniJava.g:1628:2: ( rule__Program__NameAssignment_0_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getProgramAccess().getNameAssignment_0_1()); 
            }
            // InternalMiniJava.g:1629:2: ( rule__Program__NameAssignment_0_1 )
            // InternalMiniJava.g:1629:3: rule__Program__NameAssignment_0_1
            {
            pushFollow(FOLLOW_2);
            rule__Program__NameAssignment_0_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getProgramAccess().getNameAssignment_0_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Program__Group_0__1__Impl"


    // $ANTLR start "rule__Program__Group_0__2"
    // InternalMiniJava.g:1637:1: rule__Program__Group_0__2 : rule__Program__Group_0__2__Impl ;
    public final void rule__Program__Group_0__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1641:1: ( rule__Program__Group_0__2__Impl )
            // InternalMiniJava.g:1642:2: rule__Program__Group_0__2__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Program__Group_0__2__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Program__Group_0__2"


    // $ANTLR start "rule__Program__Group_0__2__Impl"
    // InternalMiniJava.g:1648:1: rule__Program__Group_0__2__Impl : ( ';' ) ;
    public final void rule__Program__Group_0__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1652:1: ( ( ';' ) )
            // InternalMiniJava.g:1653:1: ( ';' )
            {
            // InternalMiniJava.g:1653:1: ( ';' )
            // InternalMiniJava.g:1654:2: ';'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getProgramAccess().getSemicolonKeyword_0_2()); 
            }
            match(input,11,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getProgramAccess().getSemicolonKeyword_0_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Program__Group_0__2__Impl"


    // $ANTLR start "rule__Import__Group__0"
    // InternalMiniJava.g:1664:1: rule__Import__Group__0 : rule__Import__Group__0__Impl rule__Import__Group__1 ;
    public final void rule__Import__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1668:1: ( rule__Import__Group__0__Impl rule__Import__Group__1 )
            // InternalMiniJava.g:1669:2: rule__Import__Group__0__Impl rule__Import__Group__1
            {
            pushFollow(FOLLOW_6);
            rule__Import__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Import__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Import__Group__0"


    // $ANTLR start "rule__Import__Group__0__Impl"
    // InternalMiniJava.g:1676:1: rule__Import__Group__0__Impl : ( 'import' ) ;
    public final void rule__Import__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1680:1: ( ( 'import' ) )
            // InternalMiniJava.g:1681:1: ( 'import' )
            {
            // InternalMiniJava.g:1681:1: ( 'import' )
            // InternalMiniJava.g:1682:2: 'import'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getImportAccess().getImportKeyword_0()); 
            }
            match(input,18,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getImportAccess().getImportKeyword_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Import__Group__0__Impl"


    // $ANTLR start "rule__Import__Group__1"
    // InternalMiniJava.g:1691:1: rule__Import__Group__1 : rule__Import__Group__1__Impl rule__Import__Group__2 ;
    public final void rule__Import__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1695:1: ( rule__Import__Group__1__Impl rule__Import__Group__2 )
            // InternalMiniJava.g:1696:2: rule__Import__Group__1__Impl rule__Import__Group__2
            {
            pushFollow(FOLLOW_7);
            rule__Import__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Import__Group__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Import__Group__1"


    // $ANTLR start "rule__Import__Group__1__Impl"
    // InternalMiniJava.g:1703:1: rule__Import__Group__1__Impl : ( ( rule__Import__ImportedNamespaceAssignment_1 ) ) ;
    public final void rule__Import__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1707:1: ( ( ( rule__Import__ImportedNamespaceAssignment_1 ) ) )
            // InternalMiniJava.g:1708:1: ( ( rule__Import__ImportedNamespaceAssignment_1 ) )
            {
            // InternalMiniJava.g:1708:1: ( ( rule__Import__ImportedNamespaceAssignment_1 ) )
            // InternalMiniJava.g:1709:2: ( rule__Import__ImportedNamespaceAssignment_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getImportAccess().getImportedNamespaceAssignment_1()); 
            }
            // InternalMiniJava.g:1710:2: ( rule__Import__ImportedNamespaceAssignment_1 )
            // InternalMiniJava.g:1710:3: rule__Import__ImportedNamespaceAssignment_1
            {
            pushFollow(FOLLOW_2);
            rule__Import__ImportedNamespaceAssignment_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getImportAccess().getImportedNamespaceAssignment_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Import__Group__1__Impl"


    // $ANTLR start "rule__Import__Group__2"
    // InternalMiniJava.g:1718:1: rule__Import__Group__2 : rule__Import__Group__2__Impl ;
    public final void rule__Import__Group__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1722:1: ( rule__Import__Group__2__Impl )
            // InternalMiniJava.g:1723:2: rule__Import__Group__2__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Import__Group__2__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Import__Group__2"


    // $ANTLR start "rule__Import__Group__2__Impl"
    // InternalMiniJava.g:1729:1: rule__Import__Group__2__Impl : ( ';' ) ;
    public final void rule__Import__Group__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1733:1: ( ( ';' ) )
            // InternalMiniJava.g:1734:1: ( ';' )
            {
            // InternalMiniJava.g:1734:1: ( ';' )
            // InternalMiniJava.g:1735:2: ';'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getImportAccess().getSemicolonKeyword_2()); 
            }
            match(input,11,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getImportAccess().getSemicolonKeyword_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Import__Group__2__Impl"


    // $ANTLR start "rule__QualifiedName__Group__0"
    // InternalMiniJava.g:1745:1: rule__QualifiedName__Group__0 : rule__QualifiedName__Group__0__Impl rule__QualifiedName__Group__1 ;
    public final void rule__QualifiedName__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1749:1: ( rule__QualifiedName__Group__0__Impl rule__QualifiedName__Group__1 )
            // InternalMiniJava.g:1750:2: rule__QualifiedName__Group__0__Impl rule__QualifiedName__Group__1
            {
            pushFollow(FOLLOW_8);
            rule__QualifiedName__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__QualifiedName__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__QualifiedName__Group__0"


    // $ANTLR start "rule__QualifiedName__Group__0__Impl"
    // InternalMiniJava.g:1757:1: rule__QualifiedName__Group__0__Impl : ( RULE_ID ) ;
    public final void rule__QualifiedName__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1761:1: ( ( RULE_ID ) )
            // InternalMiniJava.g:1762:1: ( RULE_ID )
            {
            // InternalMiniJava.g:1762:1: ( RULE_ID )
            // InternalMiniJava.g:1763:2: RULE_ID
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getQualifiedNameAccess().getIDTerminalRuleCall_0()); 
            }
            match(input,RULE_ID,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getQualifiedNameAccess().getIDTerminalRuleCall_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__QualifiedName__Group__0__Impl"


    // $ANTLR start "rule__QualifiedName__Group__1"
    // InternalMiniJava.g:1772:1: rule__QualifiedName__Group__1 : rule__QualifiedName__Group__1__Impl ;
    public final void rule__QualifiedName__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1776:1: ( rule__QualifiedName__Group__1__Impl )
            // InternalMiniJava.g:1777:2: rule__QualifiedName__Group__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__QualifiedName__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__QualifiedName__Group__1"


    // $ANTLR start "rule__QualifiedName__Group__1__Impl"
    // InternalMiniJava.g:1783:1: rule__QualifiedName__Group__1__Impl : ( ( rule__QualifiedName__Group_1__0 )* ) ;
    public final void rule__QualifiedName__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1787:1: ( ( ( rule__QualifiedName__Group_1__0 )* ) )
            // InternalMiniJava.g:1788:1: ( ( rule__QualifiedName__Group_1__0 )* )
            {
            // InternalMiniJava.g:1788:1: ( ( rule__QualifiedName__Group_1__0 )* )
            // InternalMiniJava.g:1789:2: ( rule__QualifiedName__Group_1__0 )*
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getQualifiedNameAccess().getGroup_1()); 
            }
            // InternalMiniJava.g:1790:2: ( rule__QualifiedName__Group_1__0 )*
            loop21:
            do {
                int alt21=2;
                int LA21_0 = input.LA(1);

                if ( (LA21_0==19) ) {
                    alt21=1;
                }


                switch (alt21) {
            	case 1 :
            	    // InternalMiniJava.g:1790:3: rule__QualifiedName__Group_1__0
            	    {
            	    pushFollow(FOLLOW_9);
            	    rule__QualifiedName__Group_1__0();

            	    state._fsp--;
            	    if (state.failed) return ;

            	    }
            	    break;

            	default :
            	    break loop21;
                }
            } while (true);

            if ( state.backtracking==0 ) {
               after(grammarAccess.getQualifiedNameAccess().getGroup_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__QualifiedName__Group__1__Impl"


    // $ANTLR start "rule__QualifiedName__Group_1__0"
    // InternalMiniJava.g:1799:1: rule__QualifiedName__Group_1__0 : rule__QualifiedName__Group_1__0__Impl rule__QualifiedName__Group_1__1 ;
    public final void rule__QualifiedName__Group_1__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1803:1: ( rule__QualifiedName__Group_1__0__Impl rule__QualifiedName__Group_1__1 )
            // InternalMiniJava.g:1804:2: rule__QualifiedName__Group_1__0__Impl rule__QualifiedName__Group_1__1
            {
            pushFollow(FOLLOW_6);
            rule__QualifiedName__Group_1__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__QualifiedName__Group_1__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__QualifiedName__Group_1__0"


    // $ANTLR start "rule__QualifiedName__Group_1__0__Impl"
    // InternalMiniJava.g:1811:1: rule__QualifiedName__Group_1__0__Impl : ( '.' ) ;
    public final void rule__QualifiedName__Group_1__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1815:1: ( ( '.' ) )
            // InternalMiniJava.g:1816:1: ( '.' )
            {
            // InternalMiniJava.g:1816:1: ( '.' )
            // InternalMiniJava.g:1817:2: '.'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getQualifiedNameAccess().getFullStopKeyword_1_0()); 
            }
            match(input,19,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getQualifiedNameAccess().getFullStopKeyword_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__QualifiedName__Group_1__0__Impl"


    // $ANTLR start "rule__QualifiedName__Group_1__1"
    // InternalMiniJava.g:1826:1: rule__QualifiedName__Group_1__1 : rule__QualifiedName__Group_1__1__Impl ;
    public final void rule__QualifiedName__Group_1__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1830:1: ( rule__QualifiedName__Group_1__1__Impl )
            // InternalMiniJava.g:1831:2: rule__QualifiedName__Group_1__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__QualifiedName__Group_1__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__QualifiedName__Group_1__1"


    // $ANTLR start "rule__QualifiedName__Group_1__1__Impl"
    // InternalMiniJava.g:1837:1: rule__QualifiedName__Group_1__1__Impl : ( RULE_ID ) ;
    public final void rule__QualifiedName__Group_1__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1841:1: ( ( RULE_ID ) )
            // InternalMiniJava.g:1842:1: ( RULE_ID )
            {
            // InternalMiniJava.g:1842:1: ( RULE_ID )
            // InternalMiniJava.g:1843:2: RULE_ID
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getQualifiedNameAccess().getIDTerminalRuleCall_1_1()); 
            }
            match(input,RULE_ID,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getQualifiedNameAccess().getIDTerminalRuleCall_1_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__QualifiedName__Group_1__1__Impl"


    // $ANTLR start "rule__QualifiedNameWithWildcard__Group__0"
    // InternalMiniJava.g:1853:1: rule__QualifiedNameWithWildcard__Group__0 : rule__QualifiedNameWithWildcard__Group__0__Impl rule__QualifiedNameWithWildcard__Group__1 ;
    public final void rule__QualifiedNameWithWildcard__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1857:1: ( rule__QualifiedNameWithWildcard__Group__0__Impl rule__QualifiedNameWithWildcard__Group__1 )
            // InternalMiniJava.g:1858:2: rule__QualifiedNameWithWildcard__Group__0__Impl rule__QualifiedNameWithWildcard__Group__1
            {
            pushFollow(FOLLOW_10);
            rule__QualifiedNameWithWildcard__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__QualifiedNameWithWildcard__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__QualifiedNameWithWildcard__Group__0"


    // $ANTLR start "rule__QualifiedNameWithWildcard__Group__0__Impl"
    // InternalMiniJava.g:1865:1: rule__QualifiedNameWithWildcard__Group__0__Impl : ( ruleQualifiedName ) ;
    public final void rule__QualifiedNameWithWildcard__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1869:1: ( ( ruleQualifiedName ) )
            // InternalMiniJava.g:1870:1: ( ruleQualifiedName )
            {
            // InternalMiniJava.g:1870:1: ( ruleQualifiedName )
            // InternalMiniJava.g:1871:2: ruleQualifiedName
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getQualifiedNameWithWildcardAccess().getQualifiedNameParserRuleCall_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleQualifiedName();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getQualifiedNameWithWildcardAccess().getQualifiedNameParserRuleCall_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__QualifiedNameWithWildcard__Group__0__Impl"


    // $ANTLR start "rule__QualifiedNameWithWildcard__Group__1"
    // InternalMiniJava.g:1880:1: rule__QualifiedNameWithWildcard__Group__1 : rule__QualifiedNameWithWildcard__Group__1__Impl ;
    public final void rule__QualifiedNameWithWildcard__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1884:1: ( rule__QualifiedNameWithWildcard__Group__1__Impl )
            // InternalMiniJava.g:1885:2: rule__QualifiedNameWithWildcard__Group__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__QualifiedNameWithWildcard__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__QualifiedNameWithWildcard__Group__1"


    // $ANTLR start "rule__QualifiedNameWithWildcard__Group__1__Impl"
    // InternalMiniJava.g:1891:1: rule__QualifiedNameWithWildcard__Group__1__Impl : ( ( '.*' )? ) ;
    public final void rule__QualifiedNameWithWildcard__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1895:1: ( ( ( '.*' )? ) )
            // InternalMiniJava.g:1896:1: ( ( '.*' )? )
            {
            // InternalMiniJava.g:1896:1: ( ( '.*' )? )
            // InternalMiniJava.g:1897:2: ( '.*' )?
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getQualifiedNameWithWildcardAccess().getFullStopAsteriskKeyword_1()); 
            }
            // InternalMiniJava.g:1898:2: ( '.*' )?
            int alt22=2;
            int LA22_0 = input.LA(1);

            if ( (LA22_0==20) ) {
                alt22=1;
            }
            switch (alt22) {
                case 1 :
                    // InternalMiniJava.g:1898:3: '.*'
                    {
                    match(input,20,FOLLOW_2); if (state.failed) return ;

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getQualifiedNameWithWildcardAccess().getFullStopAsteriskKeyword_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__QualifiedNameWithWildcard__Group__1__Impl"


    // $ANTLR start "rule__Class__Group__0"
    // InternalMiniJava.g:1907:1: rule__Class__Group__0 : rule__Class__Group__0__Impl rule__Class__Group__1 ;
    public final void rule__Class__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1911:1: ( rule__Class__Group__0__Impl rule__Class__Group__1 )
            // InternalMiniJava.g:1912:2: rule__Class__Group__0__Impl rule__Class__Group__1
            {
            pushFollow(FOLLOW_11);
            rule__Class__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Class__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group__0"


    // $ANTLR start "rule__Class__Group__0__Impl"
    // InternalMiniJava.g:1919:1: rule__Class__Group__0__Impl : ( ( rule__Class__AccessLevelAssignment_0 )? ) ;
    public final void rule__Class__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1923:1: ( ( ( rule__Class__AccessLevelAssignment_0 )? ) )
            // InternalMiniJava.g:1924:1: ( ( rule__Class__AccessLevelAssignment_0 )? )
            {
            // InternalMiniJava.g:1924:1: ( ( rule__Class__AccessLevelAssignment_0 )? )
            // InternalMiniJava.g:1925:2: ( rule__Class__AccessLevelAssignment_0 )?
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getAccessLevelAssignment_0()); 
            }
            // InternalMiniJava.g:1926:2: ( rule__Class__AccessLevelAssignment_0 )?
            int alt23=2;
            int LA23_0 = input.LA(1);

            if ( ((LA23_0>=14 && LA23_0<=16)) ) {
                alt23=1;
            }
            switch (alt23) {
                case 1 :
                    // InternalMiniJava.g:1926:3: rule__Class__AccessLevelAssignment_0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Class__AccessLevelAssignment_0();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getAccessLevelAssignment_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group__0__Impl"


    // $ANTLR start "rule__Class__Group__1"
    // InternalMiniJava.g:1934:1: rule__Class__Group__1 : rule__Class__Group__1__Impl rule__Class__Group__2 ;
    public final void rule__Class__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1938:1: ( rule__Class__Group__1__Impl rule__Class__Group__2 )
            // InternalMiniJava.g:1939:2: rule__Class__Group__1__Impl rule__Class__Group__2
            {
            pushFollow(FOLLOW_11);
            rule__Class__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Class__Group__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group__1"


    // $ANTLR start "rule__Class__Group__1__Impl"
    // InternalMiniJava.g:1946:1: rule__Class__Group__1__Impl : ( ( rule__Class__AbstractAssignment_1 )? ) ;
    public final void rule__Class__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1950:1: ( ( ( rule__Class__AbstractAssignment_1 )? ) )
            // InternalMiniJava.g:1951:1: ( ( rule__Class__AbstractAssignment_1 )? )
            {
            // InternalMiniJava.g:1951:1: ( ( rule__Class__AbstractAssignment_1 )? )
            // InternalMiniJava.g:1952:2: ( rule__Class__AbstractAssignment_1 )?
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getAbstractAssignment_1()); 
            }
            // InternalMiniJava.g:1953:2: ( rule__Class__AbstractAssignment_1 )?
            int alt24=2;
            int LA24_0 = input.LA(1);

            if ( (LA24_0==63) ) {
                alt24=1;
            }
            switch (alt24) {
                case 1 :
                    // InternalMiniJava.g:1953:3: rule__Class__AbstractAssignment_1
                    {
                    pushFollow(FOLLOW_2);
                    rule__Class__AbstractAssignment_1();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getAbstractAssignment_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group__1__Impl"


    // $ANTLR start "rule__Class__Group__2"
    // InternalMiniJava.g:1961:1: rule__Class__Group__2 : rule__Class__Group__2__Impl rule__Class__Group__3 ;
    public final void rule__Class__Group__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1965:1: ( rule__Class__Group__2__Impl rule__Class__Group__3 )
            // InternalMiniJava.g:1966:2: rule__Class__Group__2__Impl rule__Class__Group__3
            {
            pushFollow(FOLLOW_6);
            rule__Class__Group__2__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Class__Group__3();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group__2"


    // $ANTLR start "rule__Class__Group__2__Impl"
    // InternalMiniJava.g:1973:1: rule__Class__Group__2__Impl : ( 'class' ) ;
    public final void rule__Class__Group__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1977:1: ( ( 'class' ) )
            // InternalMiniJava.g:1978:1: ( 'class' )
            {
            // InternalMiniJava.g:1978:1: ( 'class' )
            // InternalMiniJava.g:1979:2: 'class'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getClassKeyword_2()); 
            }
            match(input,21,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getClassKeyword_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group__2__Impl"


    // $ANTLR start "rule__Class__Group__3"
    // InternalMiniJava.g:1988:1: rule__Class__Group__3 : rule__Class__Group__3__Impl rule__Class__Group__4 ;
    public final void rule__Class__Group__3() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:1992:1: ( rule__Class__Group__3__Impl rule__Class__Group__4 )
            // InternalMiniJava.g:1993:2: rule__Class__Group__3__Impl rule__Class__Group__4
            {
            pushFollow(FOLLOW_12);
            rule__Class__Group__3__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Class__Group__4();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group__3"


    // $ANTLR start "rule__Class__Group__3__Impl"
    // InternalMiniJava.g:2000:1: rule__Class__Group__3__Impl : ( ( rule__Class__NameAssignment_3 ) ) ;
    public final void rule__Class__Group__3__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2004:1: ( ( ( rule__Class__NameAssignment_3 ) ) )
            // InternalMiniJava.g:2005:1: ( ( rule__Class__NameAssignment_3 ) )
            {
            // InternalMiniJava.g:2005:1: ( ( rule__Class__NameAssignment_3 ) )
            // InternalMiniJava.g:2006:2: ( rule__Class__NameAssignment_3 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getNameAssignment_3()); 
            }
            // InternalMiniJava.g:2007:2: ( rule__Class__NameAssignment_3 )
            // InternalMiniJava.g:2007:3: rule__Class__NameAssignment_3
            {
            pushFollow(FOLLOW_2);
            rule__Class__NameAssignment_3();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getNameAssignment_3()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group__3__Impl"


    // $ANTLR start "rule__Class__Group__4"
    // InternalMiniJava.g:2015:1: rule__Class__Group__4 : rule__Class__Group__4__Impl rule__Class__Group__5 ;
    public final void rule__Class__Group__4() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2019:1: ( rule__Class__Group__4__Impl rule__Class__Group__5 )
            // InternalMiniJava.g:2020:2: rule__Class__Group__4__Impl rule__Class__Group__5
            {
            pushFollow(FOLLOW_12);
            rule__Class__Group__4__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Class__Group__5();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group__4"


    // $ANTLR start "rule__Class__Group__4__Impl"
    // InternalMiniJava.g:2027:1: rule__Class__Group__4__Impl : ( ( rule__Class__Group_4__0 )? ) ;
    public final void rule__Class__Group__4__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2031:1: ( ( ( rule__Class__Group_4__0 )? ) )
            // InternalMiniJava.g:2032:1: ( ( rule__Class__Group_4__0 )? )
            {
            // InternalMiniJava.g:2032:1: ( ( rule__Class__Group_4__0 )? )
            // InternalMiniJava.g:2033:2: ( rule__Class__Group_4__0 )?
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getGroup_4()); 
            }
            // InternalMiniJava.g:2034:2: ( rule__Class__Group_4__0 )?
            int alt25=2;
            int LA25_0 = input.LA(1);

            if ( (LA25_0==24) ) {
                alt25=1;
            }
            switch (alt25) {
                case 1 :
                    // InternalMiniJava.g:2034:3: rule__Class__Group_4__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Class__Group_4__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getGroup_4()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group__4__Impl"


    // $ANTLR start "rule__Class__Group__5"
    // InternalMiniJava.g:2042:1: rule__Class__Group__5 : rule__Class__Group__5__Impl rule__Class__Group__6 ;
    public final void rule__Class__Group__5() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2046:1: ( rule__Class__Group__5__Impl rule__Class__Group__6 )
            // InternalMiniJava.g:2047:2: rule__Class__Group__5__Impl rule__Class__Group__6
            {
            pushFollow(FOLLOW_12);
            rule__Class__Group__5__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Class__Group__6();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group__5"


    // $ANTLR start "rule__Class__Group__5__Impl"
    // InternalMiniJava.g:2054:1: rule__Class__Group__5__Impl : ( ( rule__Class__Group_5__0 )? ) ;
    public final void rule__Class__Group__5__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2058:1: ( ( ( rule__Class__Group_5__0 )? ) )
            // InternalMiniJava.g:2059:1: ( ( rule__Class__Group_5__0 )? )
            {
            // InternalMiniJava.g:2059:1: ( ( rule__Class__Group_5__0 )? )
            // InternalMiniJava.g:2060:2: ( rule__Class__Group_5__0 )?
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getGroup_5()); 
            }
            // InternalMiniJava.g:2061:2: ( rule__Class__Group_5__0 )?
            int alt26=2;
            int LA26_0 = input.LA(1);

            if ( (LA26_0==25) ) {
                alt26=1;
            }
            switch (alt26) {
                case 1 :
                    // InternalMiniJava.g:2061:3: rule__Class__Group_5__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Class__Group_5__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getGroup_5()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group__5__Impl"


    // $ANTLR start "rule__Class__Group__6"
    // InternalMiniJava.g:2069:1: rule__Class__Group__6 : rule__Class__Group__6__Impl rule__Class__Group__7 ;
    public final void rule__Class__Group__6() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2073:1: ( rule__Class__Group__6__Impl rule__Class__Group__7 )
            // InternalMiniJava.g:2074:2: rule__Class__Group__6__Impl rule__Class__Group__7
            {
            pushFollow(FOLLOW_13);
            rule__Class__Group__6__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Class__Group__7();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group__6"


    // $ANTLR start "rule__Class__Group__6__Impl"
    // InternalMiniJava.g:2081:1: rule__Class__Group__6__Impl : ( '{' ) ;
    public final void rule__Class__Group__6__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2085:1: ( ( '{' ) )
            // InternalMiniJava.g:2086:1: ( '{' )
            {
            // InternalMiniJava.g:2086:1: ( '{' )
            // InternalMiniJava.g:2087:2: '{'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getLeftCurlyBracketKeyword_6()); 
            }
            match(input,22,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getLeftCurlyBracketKeyword_6()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group__6__Impl"


    // $ANTLR start "rule__Class__Group__7"
    // InternalMiniJava.g:2096:1: rule__Class__Group__7 : rule__Class__Group__7__Impl rule__Class__Group__8 ;
    public final void rule__Class__Group__7() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2100:1: ( rule__Class__Group__7__Impl rule__Class__Group__8 )
            // InternalMiniJava.g:2101:2: rule__Class__Group__7__Impl rule__Class__Group__8
            {
            pushFollow(FOLLOW_13);
            rule__Class__Group__7__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Class__Group__8();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group__7"


    // $ANTLR start "rule__Class__Group__7__Impl"
    // InternalMiniJava.g:2108:1: rule__Class__Group__7__Impl : ( ( rule__Class__MembersAssignment_7 )* ) ;
    public final void rule__Class__Group__7__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2112:1: ( ( ( rule__Class__MembersAssignment_7 )* ) )
            // InternalMiniJava.g:2113:1: ( ( rule__Class__MembersAssignment_7 )* )
            {
            // InternalMiniJava.g:2113:1: ( ( rule__Class__MembersAssignment_7 )* )
            // InternalMiniJava.g:2114:2: ( rule__Class__MembersAssignment_7 )*
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getMembersAssignment_7()); 
            }
            // InternalMiniJava.g:2115:2: ( rule__Class__MembersAssignment_7 )*
            loop27:
            do {
                int alt27=2;
                int LA27_0 = input.LA(1);

                if ( (LA27_0==RULE_ID||(LA27_0>=14 && LA27_0<=16)||(LA27_0>=41 && LA27_0<=44)||(LA27_0>=63 && LA27_0<=64)) ) {
                    alt27=1;
                }


                switch (alt27) {
            	case 1 :
            	    // InternalMiniJava.g:2115:3: rule__Class__MembersAssignment_7
            	    {
            	    pushFollow(FOLLOW_14);
            	    rule__Class__MembersAssignment_7();

            	    state._fsp--;
            	    if (state.failed) return ;

            	    }
            	    break;

            	default :
            	    break loop27;
                }
            } while (true);

            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getMembersAssignment_7()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group__7__Impl"


    // $ANTLR start "rule__Class__Group__8"
    // InternalMiniJava.g:2123:1: rule__Class__Group__8 : rule__Class__Group__8__Impl ;
    public final void rule__Class__Group__8() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2127:1: ( rule__Class__Group__8__Impl )
            // InternalMiniJava.g:2128:2: rule__Class__Group__8__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Class__Group__8__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group__8"


    // $ANTLR start "rule__Class__Group__8__Impl"
    // InternalMiniJava.g:2134:1: rule__Class__Group__8__Impl : ( '}' ) ;
    public final void rule__Class__Group__8__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2138:1: ( ( '}' ) )
            // InternalMiniJava.g:2139:1: ( '}' )
            {
            // InternalMiniJava.g:2139:1: ( '}' )
            // InternalMiniJava.g:2140:2: '}'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getRightCurlyBracketKeyword_8()); 
            }
            match(input,23,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getRightCurlyBracketKeyword_8()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group__8__Impl"


    // $ANTLR start "rule__Class__Group_4__0"
    // InternalMiniJava.g:2150:1: rule__Class__Group_4__0 : rule__Class__Group_4__0__Impl rule__Class__Group_4__1 ;
    public final void rule__Class__Group_4__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2154:1: ( rule__Class__Group_4__0__Impl rule__Class__Group_4__1 )
            // InternalMiniJava.g:2155:2: rule__Class__Group_4__0__Impl rule__Class__Group_4__1
            {
            pushFollow(FOLLOW_6);
            rule__Class__Group_4__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Class__Group_4__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group_4__0"


    // $ANTLR start "rule__Class__Group_4__0__Impl"
    // InternalMiniJava.g:2162:1: rule__Class__Group_4__0__Impl : ( 'extends' ) ;
    public final void rule__Class__Group_4__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2166:1: ( ( 'extends' ) )
            // InternalMiniJava.g:2167:1: ( 'extends' )
            {
            // InternalMiniJava.g:2167:1: ( 'extends' )
            // InternalMiniJava.g:2168:2: 'extends'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getExtendsKeyword_4_0()); 
            }
            match(input,24,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getExtendsKeyword_4_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group_4__0__Impl"


    // $ANTLR start "rule__Class__Group_4__1"
    // InternalMiniJava.g:2177:1: rule__Class__Group_4__1 : rule__Class__Group_4__1__Impl ;
    public final void rule__Class__Group_4__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2181:1: ( rule__Class__Group_4__1__Impl )
            // InternalMiniJava.g:2182:2: rule__Class__Group_4__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Class__Group_4__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group_4__1"


    // $ANTLR start "rule__Class__Group_4__1__Impl"
    // InternalMiniJava.g:2188:1: rule__Class__Group_4__1__Impl : ( ( rule__Class__SuperClassAssignment_4_1 ) ) ;
    public final void rule__Class__Group_4__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2192:1: ( ( ( rule__Class__SuperClassAssignment_4_1 ) ) )
            // InternalMiniJava.g:2193:1: ( ( rule__Class__SuperClassAssignment_4_1 ) )
            {
            // InternalMiniJava.g:2193:1: ( ( rule__Class__SuperClassAssignment_4_1 ) )
            // InternalMiniJava.g:2194:2: ( rule__Class__SuperClassAssignment_4_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getSuperClassAssignment_4_1()); 
            }
            // InternalMiniJava.g:2195:2: ( rule__Class__SuperClassAssignment_4_1 )
            // InternalMiniJava.g:2195:3: rule__Class__SuperClassAssignment_4_1
            {
            pushFollow(FOLLOW_2);
            rule__Class__SuperClassAssignment_4_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getSuperClassAssignment_4_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group_4__1__Impl"


    // $ANTLR start "rule__Class__Group_5__0"
    // InternalMiniJava.g:2204:1: rule__Class__Group_5__0 : rule__Class__Group_5__0__Impl rule__Class__Group_5__1 ;
    public final void rule__Class__Group_5__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2208:1: ( rule__Class__Group_5__0__Impl rule__Class__Group_5__1 )
            // InternalMiniJava.g:2209:2: rule__Class__Group_5__0__Impl rule__Class__Group_5__1
            {
            pushFollow(FOLLOW_6);
            rule__Class__Group_5__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Class__Group_5__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group_5__0"


    // $ANTLR start "rule__Class__Group_5__0__Impl"
    // InternalMiniJava.g:2216:1: rule__Class__Group_5__0__Impl : ( 'implements' ) ;
    public final void rule__Class__Group_5__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2220:1: ( ( 'implements' ) )
            // InternalMiniJava.g:2221:1: ( 'implements' )
            {
            // InternalMiniJava.g:2221:1: ( 'implements' )
            // InternalMiniJava.g:2222:2: 'implements'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getImplementsKeyword_5_0()); 
            }
            match(input,25,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getImplementsKeyword_5_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group_5__0__Impl"


    // $ANTLR start "rule__Class__Group_5__1"
    // InternalMiniJava.g:2231:1: rule__Class__Group_5__1 : rule__Class__Group_5__1__Impl rule__Class__Group_5__2 ;
    public final void rule__Class__Group_5__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2235:1: ( rule__Class__Group_5__1__Impl rule__Class__Group_5__2 )
            // InternalMiniJava.g:2236:2: rule__Class__Group_5__1__Impl rule__Class__Group_5__2
            {
            pushFollow(FOLLOW_15);
            rule__Class__Group_5__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Class__Group_5__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group_5__1"


    // $ANTLR start "rule__Class__Group_5__1__Impl"
    // InternalMiniJava.g:2243:1: rule__Class__Group_5__1__Impl : ( ( rule__Class__ImplementsAssignment_5_1 ) ) ;
    public final void rule__Class__Group_5__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2247:1: ( ( ( rule__Class__ImplementsAssignment_5_1 ) ) )
            // InternalMiniJava.g:2248:1: ( ( rule__Class__ImplementsAssignment_5_1 ) )
            {
            // InternalMiniJava.g:2248:1: ( ( rule__Class__ImplementsAssignment_5_1 ) )
            // InternalMiniJava.g:2249:2: ( rule__Class__ImplementsAssignment_5_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getImplementsAssignment_5_1()); 
            }
            // InternalMiniJava.g:2250:2: ( rule__Class__ImplementsAssignment_5_1 )
            // InternalMiniJava.g:2250:3: rule__Class__ImplementsAssignment_5_1
            {
            pushFollow(FOLLOW_2);
            rule__Class__ImplementsAssignment_5_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getImplementsAssignment_5_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group_5__1__Impl"


    // $ANTLR start "rule__Class__Group_5__2"
    // InternalMiniJava.g:2258:1: rule__Class__Group_5__2 : rule__Class__Group_5__2__Impl ;
    public final void rule__Class__Group_5__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2262:1: ( rule__Class__Group_5__2__Impl )
            // InternalMiniJava.g:2263:2: rule__Class__Group_5__2__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Class__Group_5__2__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group_5__2"


    // $ANTLR start "rule__Class__Group_5__2__Impl"
    // InternalMiniJava.g:2269:1: rule__Class__Group_5__2__Impl : ( ( rule__Class__Group_5_2__0 )* ) ;
    public final void rule__Class__Group_5__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2273:1: ( ( ( rule__Class__Group_5_2__0 )* ) )
            // InternalMiniJava.g:2274:1: ( ( rule__Class__Group_5_2__0 )* )
            {
            // InternalMiniJava.g:2274:1: ( ( rule__Class__Group_5_2__0 )* )
            // InternalMiniJava.g:2275:2: ( rule__Class__Group_5_2__0 )*
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getGroup_5_2()); 
            }
            // InternalMiniJava.g:2276:2: ( rule__Class__Group_5_2__0 )*
            loop28:
            do {
                int alt28=2;
                int LA28_0 = input.LA(1);

                if ( (LA28_0==26) ) {
                    alt28=1;
                }


                switch (alt28) {
            	case 1 :
            	    // InternalMiniJava.g:2276:3: rule__Class__Group_5_2__0
            	    {
            	    pushFollow(FOLLOW_16);
            	    rule__Class__Group_5_2__0();

            	    state._fsp--;
            	    if (state.failed) return ;

            	    }
            	    break;

            	default :
            	    break loop28;
                }
            } while (true);

            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getGroup_5_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group_5__2__Impl"


    // $ANTLR start "rule__Class__Group_5_2__0"
    // InternalMiniJava.g:2285:1: rule__Class__Group_5_2__0 : rule__Class__Group_5_2__0__Impl rule__Class__Group_5_2__1 ;
    public final void rule__Class__Group_5_2__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2289:1: ( rule__Class__Group_5_2__0__Impl rule__Class__Group_5_2__1 )
            // InternalMiniJava.g:2290:2: rule__Class__Group_5_2__0__Impl rule__Class__Group_5_2__1
            {
            pushFollow(FOLLOW_6);
            rule__Class__Group_5_2__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Class__Group_5_2__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group_5_2__0"


    // $ANTLR start "rule__Class__Group_5_2__0__Impl"
    // InternalMiniJava.g:2297:1: rule__Class__Group_5_2__0__Impl : ( ',' ) ;
    public final void rule__Class__Group_5_2__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2301:1: ( ( ',' ) )
            // InternalMiniJava.g:2302:1: ( ',' )
            {
            // InternalMiniJava.g:2302:1: ( ',' )
            // InternalMiniJava.g:2303:2: ','
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getCommaKeyword_5_2_0()); 
            }
            match(input,26,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getCommaKeyword_5_2_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group_5_2__0__Impl"


    // $ANTLR start "rule__Class__Group_5_2__1"
    // InternalMiniJava.g:2312:1: rule__Class__Group_5_2__1 : rule__Class__Group_5_2__1__Impl ;
    public final void rule__Class__Group_5_2__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2316:1: ( rule__Class__Group_5_2__1__Impl )
            // InternalMiniJava.g:2317:2: rule__Class__Group_5_2__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Class__Group_5_2__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group_5_2__1"


    // $ANTLR start "rule__Class__Group_5_2__1__Impl"
    // InternalMiniJava.g:2323:1: rule__Class__Group_5_2__1__Impl : ( ( rule__Class__ImplementsAssignment_5_2_1 ) ) ;
    public final void rule__Class__Group_5_2__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2327:1: ( ( ( rule__Class__ImplementsAssignment_5_2_1 ) ) )
            // InternalMiniJava.g:2328:1: ( ( rule__Class__ImplementsAssignment_5_2_1 ) )
            {
            // InternalMiniJava.g:2328:1: ( ( rule__Class__ImplementsAssignment_5_2_1 ) )
            // InternalMiniJava.g:2329:2: ( rule__Class__ImplementsAssignment_5_2_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getImplementsAssignment_5_2_1()); 
            }
            // InternalMiniJava.g:2330:2: ( rule__Class__ImplementsAssignment_5_2_1 )
            // InternalMiniJava.g:2330:3: rule__Class__ImplementsAssignment_5_2_1
            {
            pushFollow(FOLLOW_2);
            rule__Class__ImplementsAssignment_5_2_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getImplementsAssignment_5_2_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__Group_5_2__1__Impl"


    // $ANTLR start "rule__Interface__Group__0"
    // InternalMiniJava.g:2339:1: rule__Interface__Group__0 : rule__Interface__Group__0__Impl rule__Interface__Group__1 ;
    public final void rule__Interface__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2343:1: ( rule__Interface__Group__0__Impl rule__Interface__Group__1 )
            // InternalMiniJava.g:2344:2: rule__Interface__Group__0__Impl rule__Interface__Group__1
            {
            pushFollow(FOLLOW_17);
            rule__Interface__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Interface__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group__0"


    // $ANTLR start "rule__Interface__Group__0__Impl"
    // InternalMiniJava.g:2351:1: rule__Interface__Group__0__Impl : ( ( rule__Interface__AccessLevelAssignment_0 )? ) ;
    public final void rule__Interface__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2355:1: ( ( ( rule__Interface__AccessLevelAssignment_0 )? ) )
            // InternalMiniJava.g:2356:1: ( ( rule__Interface__AccessLevelAssignment_0 )? )
            {
            // InternalMiniJava.g:2356:1: ( ( rule__Interface__AccessLevelAssignment_0 )? )
            // InternalMiniJava.g:2357:2: ( rule__Interface__AccessLevelAssignment_0 )?
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getInterfaceAccess().getAccessLevelAssignment_0()); 
            }
            // InternalMiniJava.g:2358:2: ( rule__Interface__AccessLevelAssignment_0 )?
            int alt29=2;
            int LA29_0 = input.LA(1);

            if ( ((LA29_0>=14 && LA29_0<=16)) ) {
                alt29=1;
            }
            switch (alt29) {
                case 1 :
                    // InternalMiniJava.g:2358:3: rule__Interface__AccessLevelAssignment_0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Interface__AccessLevelAssignment_0();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getInterfaceAccess().getAccessLevelAssignment_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group__0__Impl"


    // $ANTLR start "rule__Interface__Group__1"
    // InternalMiniJava.g:2366:1: rule__Interface__Group__1 : rule__Interface__Group__1__Impl rule__Interface__Group__2 ;
    public final void rule__Interface__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2370:1: ( rule__Interface__Group__1__Impl rule__Interface__Group__2 )
            // InternalMiniJava.g:2371:2: rule__Interface__Group__1__Impl rule__Interface__Group__2
            {
            pushFollow(FOLLOW_6);
            rule__Interface__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Interface__Group__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group__1"


    // $ANTLR start "rule__Interface__Group__1__Impl"
    // InternalMiniJava.g:2378:1: rule__Interface__Group__1__Impl : ( 'interface' ) ;
    public final void rule__Interface__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2382:1: ( ( 'interface' ) )
            // InternalMiniJava.g:2383:1: ( 'interface' )
            {
            // InternalMiniJava.g:2383:1: ( 'interface' )
            // InternalMiniJava.g:2384:2: 'interface'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getInterfaceAccess().getInterfaceKeyword_1()); 
            }
            match(input,27,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getInterfaceAccess().getInterfaceKeyword_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group__1__Impl"


    // $ANTLR start "rule__Interface__Group__2"
    // InternalMiniJava.g:2393:1: rule__Interface__Group__2 : rule__Interface__Group__2__Impl rule__Interface__Group__3 ;
    public final void rule__Interface__Group__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2397:1: ( rule__Interface__Group__2__Impl rule__Interface__Group__3 )
            // InternalMiniJava.g:2398:2: rule__Interface__Group__2__Impl rule__Interface__Group__3
            {
            pushFollow(FOLLOW_18);
            rule__Interface__Group__2__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Interface__Group__3();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group__2"


    // $ANTLR start "rule__Interface__Group__2__Impl"
    // InternalMiniJava.g:2405:1: rule__Interface__Group__2__Impl : ( ( rule__Interface__NameAssignment_2 ) ) ;
    public final void rule__Interface__Group__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2409:1: ( ( ( rule__Interface__NameAssignment_2 ) ) )
            // InternalMiniJava.g:2410:1: ( ( rule__Interface__NameAssignment_2 ) )
            {
            // InternalMiniJava.g:2410:1: ( ( rule__Interface__NameAssignment_2 ) )
            // InternalMiniJava.g:2411:2: ( rule__Interface__NameAssignment_2 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getInterfaceAccess().getNameAssignment_2()); 
            }
            // InternalMiniJava.g:2412:2: ( rule__Interface__NameAssignment_2 )
            // InternalMiniJava.g:2412:3: rule__Interface__NameAssignment_2
            {
            pushFollow(FOLLOW_2);
            rule__Interface__NameAssignment_2();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getInterfaceAccess().getNameAssignment_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group__2__Impl"


    // $ANTLR start "rule__Interface__Group__3"
    // InternalMiniJava.g:2420:1: rule__Interface__Group__3 : rule__Interface__Group__3__Impl rule__Interface__Group__4 ;
    public final void rule__Interface__Group__3() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2424:1: ( rule__Interface__Group__3__Impl rule__Interface__Group__4 )
            // InternalMiniJava.g:2425:2: rule__Interface__Group__3__Impl rule__Interface__Group__4
            {
            pushFollow(FOLLOW_18);
            rule__Interface__Group__3__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Interface__Group__4();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group__3"


    // $ANTLR start "rule__Interface__Group__3__Impl"
    // InternalMiniJava.g:2432:1: rule__Interface__Group__3__Impl : ( ( rule__Interface__Group_3__0 )? ) ;
    public final void rule__Interface__Group__3__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2436:1: ( ( ( rule__Interface__Group_3__0 )? ) )
            // InternalMiniJava.g:2437:1: ( ( rule__Interface__Group_3__0 )? )
            {
            // InternalMiniJava.g:2437:1: ( ( rule__Interface__Group_3__0 )? )
            // InternalMiniJava.g:2438:2: ( rule__Interface__Group_3__0 )?
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getInterfaceAccess().getGroup_3()); 
            }
            // InternalMiniJava.g:2439:2: ( rule__Interface__Group_3__0 )?
            int alt30=2;
            int LA30_0 = input.LA(1);

            if ( (LA30_0==24) ) {
                alt30=1;
            }
            switch (alt30) {
                case 1 :
                    // InternalMiniJava.g:2439:3: rule__Interface__Group_3__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Interface__Group_3__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getInterfaceAccess().getGroup_3()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group__3__Impl"


    // $ANTLR start "rule__Interface__Group__4"
    // InternalMiniJava.g:2447:1: rule__Interface__Group__4 : rule__Interface__Group__4__Impl rule__Interface__Group__5 ;
    public final void rule__Interface__Group__4() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2451:1: ( rule__Interface__Group__4__Impl rule__Interface__Group__5 )
            // InternalMiniJava.g:2452:2: rule__Interface__Group__4__Impl rule__Interface__Group__5
            {
            pushFollow(FOLLOW_13);
            rule__Interface__Group__4__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Interface__Group__5();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group__4"


    // $ANTLR start "rule__Interface__Group__4__Impl"
    // InternalMiniJava.g:2459:1: rule__Interface__Group__4__Impl : ( '{' ) ;
    public final void rule__Interface__Group__4__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2463:1: ( ( '{' ) )
            // InternalMiniJava.g:2464:1: ( '{' )
            {
            // InternalMiniJava.g:2464:1: ( '{' )
            // InternalMiniJava.g:2465:2: '{'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getInterfaceAccess().getLeftCurlyBracketKeyword_4()); 
            }
            match(input,22,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getInterfaceAccess().getLeftCurlyBracketKeyword_4()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group__4__Impl"


    // $ANTLR start "rule__Interface__Group__5"
    // InternalMiniJava.g:2474:1: rule__Interface__Group__5 : rule__Interface__Group__5__Impl rule__Interface__Group__6 ;
    public final void rule__Interface__Group__5() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2478:1: ( rule__Interface__Group__5__Impl rule__Interface__Group__6 )
            // InternalMiniJava.g:2479:2: rule__Interface__Group__5__Impl rule__Interface__Group__6
            {
            pushFollow(FOLLOW_13);
            rule__Interface__Group__5__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Interface__Group__6();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group__5"


    // $ANTLR start "rule__Interface__Group__5__Impl"
    // InternalMiniJava.g:2486:1: rule__Interface__Group__5__Impl : ( ( rule__Interface__MembersAssignment_5 )* ) ;
    public final void rule__Interface__Group__5__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2490:1: ( ( ( rule__Interface__MembersAssignment_5 )* ) )
            // InternalMiniJava.g:2491:1: ( ( rule__Interface__MembersAssignment_5 )* )
            {
            // InternalMiniJava.g:2491:1: ( ( rule__Interface__MembersAssignment_5 )* )
            // InternalMiniJava.g:2492:2: ( rule__Interface__MembersAssignment_5 )*
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getInterfaceAccess().getMembersAssignment_5()); 
            }
            // InternalMiniJava.g:2493:2: ( rule__Interface__MembersAssignment_5 )*
            loop31:
            do {
                int alt31=2;
                int LA31_0 = input.LA(1);

                if ( (LA31_0==RULE_ID||(LA31_0>=14 && LA31_0<=16)||(LA31_0>=41 && LA31_0<=44)||(LA31_0>=63 && LA31_0<=64)) ) {
                    alt31=1;
                }


                switch (alt31) {
            	case 1 :
            	    // InternalMiniJava.g:2493:3: rule__Interface__MembersAssignment_5
            	    {
            	    pushFollow(FOLLOW_14);
            	    rule__Interface__MembersAssignment_5();

            	    state._fsp--;
            	    if (state.failed) return ;

            	    }
            	    break;

            	default :
            	    break loop31;
                }
            } while (true);

            if ( state.backtracking==0 ) {
               after(grammarAccess.getInterfaceAccess().getMembersAssignment_5()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group__5__Impl"


    // $ANTLR start "rule__Interface__Group__6"
    // InternalMiniJava.g:2501:1: rule__Interface__Group__6 : rule__Interface__Group__6__Impl ;
    public final void rule__Interface__Group__6() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2505:1: ( rule__Interface__Group__6__Impl )
            // InternalMiniJava.g:2506:2: rule__Interface__Group__6__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Interface__Group__6__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group__6"


    // $ANTLR start "rule__Interface__Group__6__Impl"
    // InternalMiniJava.g:2512:1: rule__Interface__Group__6__Impl : ( '}' ) ;
    public final void rule__Interface__Group__6__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2516:1: ( ( '}' ) )
            // InternalMiniJava.g:2517:1: ( '}' )
            {
            // InternalMiniJava.g:2517:1: ( '}' )
            // InternalMiniJava.g:2518:2: '}'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getInterfaceAccess().getRightCurlyBracketKeyword_6()); 
            }
            match(input,23,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getInterfaceAccess().getRightCurlyBracketKeyword_6()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group__6__Impl"


    // $ANTLR start "rule__Interface__Group_3__0"
    // InternalMiniJava.g:2528:1: rule__Interface__Group_3__0 : rule__Interface__Group_3__0__Impl rule__Interface__Group_3__1 ;
    public final void rule__Interface__Group_3__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2532:1: ( rule__Interface__Group_3__0__Impl rule__Interface__Group_3__1 )
            // InternalMiniJava.g:2533:2: rule__Interface__Group_3__0__Impl rule__Interface__Group_3__1
            {
            pushFollow(FOLLOW_6);
            rule__Interface__Group_3__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Interface__Group_3__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group_3__0"


    // $ANTLR start "rule__Interface__Group_3__0__Impl"
    // InternalMiniJava.g:2540:1: rule__Interface__Group_3__0__Impl : ( 'extends' ) ;
    public final void rule__Interface__Group_3__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2544:1: ( ( 'extends' ) )
            // InternalMiniJava.g:2545:1: ( 'extends' )
            {
            // InternalMiniJava.g:2545:1: ( 'extends' )
            // InternalMiniJava.g:2546:2: 'extends'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getInterfaceAccess().getExtendsKeyword_3_0()); 
            }
            match(input,24,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getInterfaceAccess().getExtendsKeyword_3_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group_3__0__Impl"


    // $ANTLR start "rule__Interface__Group_3__1"
    // InternalMiniJava.g:2555:1: rule__Interface__Group_3__1 : rule__Interface__Group_3__1__Impl rule__Interface__Group_3__2 ;
    public final void rule__Interface__Group_3__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2559:1: ( rule__Interface__Group_3__1__Impl rule__Interface__Group_3__2 )
            // InternalMiniJava.g:2560:2: rule__Interface__Group_3__1__Impl rule__Interface__Group_3__2
            {
            pushFollow(FOLLOW_15);
            rule__Interface__Group_3__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Interface__Group_3__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group_3__1"


    // $ANTLR start "rule__Interface__Group_3__1__Impl"
    // InternalMiniJava.g:2567:1: rule__Interface__Group_3__1__Impl : ( ( rule__Interface__ImplementsAssignment_3_1 ) ) ;
    public final void rule__Interface__Group_3__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2571:1: ( ( ( rule__Interface__ImplementsAssignment_3_1 ) ) )
            // InternalMiniJava.g:2572:1: ( ( rule__Interface__ImplementsAssignment_3_1 ) )
            {
            // InternalMiniJava.g:2572:1: ( ( rule__Interface__ImplementsAssignment_3_1 ) )
            // InternalMiniJava.g:2573:2: ( rule__Interface__ImplementsAssignment_3_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getInterfaceAccess().getImplementsAssignment_3_1()); 
            }
            // InternalMiniJava.g:2574:2: ( rule__Interface__ImplementsAssignment_3_1 )
            // InternalMiniJava.g:2574:3: rule__Interface__ImplementsAssignment_3_1
            {
            pushFollow(FOLLOW_2);
            rule__Interface__ImplementsAssignment_3_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getInterfaceAccess().getImplementsAssignment_3_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group_3__1__Impl"


    // $ANTLR start "rule__Interface__Group_3__2"
    // InternalMiniJava.g:2582:1: rule__Interface__Group_3__2 : rule__Interface__Group_3__2__Impl ;
    public final void rule__Interface__Group_3__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2586:1: ( rule__Interface__Group_3__2__Impl )
            // InternalMiniJava.g:2587:2: rule__Interface__Group_3__2__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Interface__Group_3__2__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group_3__2"


    // $ANTLR start "rule__Interface__Group_3__2__Impl"
    // InternalMiniJava.g:2593:1: rule__Interface__Group_3__2__Impl : ( ( rule__Interface__Group_3_2__0 )* ) ;
    public final void rule__Interface__Group_3__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2597:1: ( ( ( rule__Interface__Group_3_2__0 )* ) )
            // InternalMiniJava.g:2598:1: ( ( rule__Interface__Group_3_2__0 )* )
            {
            // InternalMiniJava.g:2598:1: ( ( rule__Interface__Group_3_2__0 )* )
            // InternalMiniJava.g:2599:2: ( rule__Interface__Group_3_2__0 )*
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getInterfaceAccess().getGroup_3_2()); 
            }
            // InternalMiniJava.g:2600:2: ( rule__Interface__Group_3_2__0 )*
            loop32:
            do {
                int alt32=2;
                int LA32_0 = input.LA(1);

                if ( (LA32_0==26) ) {
                    alt32=1;
                }


                switch (alt32) {
            	case 1 :
            	    // InternalMiniJava.g:2600:3: rule__Interface__Group_3_2__0
            	    {
            	    pushFollow(FOLLOW_16);
            	    rule__Interface__Group_3_2__0();

            	    state._fsp--;
            	    if (state.failed) return ;

            	    }
            	    break;

            	default :
            	    break loop32;
                }
            } while (true);

            if ( state.backtracking==0 ) {
               after(grammarAccess.getInterfaceAccess().getGroup_3_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group_3__2__Impl"


    // $ANTLR start "rule__Interface__Group_3_2__0"
    // InternalMiniJava.g:2609:1: rule__Interface__Group_3_2__0 : rule__Interface__Group_3_2__0__Impl rule__Interface__Group_3_2__1 ;
    public final void rule__Interface__Group_3_2__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2613:1: ( rule__Interface__Group_3_2__0__Impl rule__Interface__Group_3_2__1 )
            // InternalMiniJava.g:2614:2: rule__Interface__Group_3_2__0__Impl rule__Interface__Group_3_2__1
            {
            pushFollow(FOLLOW_6);
            rule__Interface__Group_3_2__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Interface__Group_3_2__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group_3_2__0"


    // $ANTLR start "rule__Interface__Group_3_2__0__Impl"
    // InternalMiniJava.g:2621:1: rule__Interface__Group_3_2__0__Impl : ( ',' ) ;
    public final void rule__Interface__Group_3_2__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2625:1: ( ( ',' ) )
            // InternalMiniJava.g:2626:1: ( ',' )
            {
            // InternalMiniJava.g:2626:1: ( ',' )
            // InternalMiniJava.g:2627:2: ','
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getInterfaceAccess().getCommaKeyword_3_2_0()); 
            }
            match(input,26,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getInterfaceAccess().getCommaKeyword_3_2_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group_3_2__0__Impl"


    // $ANTLR start "rule__Interface__Group_3_2__1"
    // InternalMiniJava.g:2636:1: rule__Interface__Group_3_2__1 : rule__Interface__Group_3_2__1__Impl ;
    public final void rule__Interface__Group_3_2__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2640:1: ( rule__Interface__Group_3_2__1__Impl )
            // InternalMiniJava.g:2641:2: rule__Interface__Group_3_2__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Interface__Group_3_2__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group_3_2__1"


    // $ANTLR start "rule__Interface__Group_3_2__1__Impl"
    // InternalMiniJava.g:2647:1: rule__Interface__Group_3_2__1__Impl : ( ( rule__Interface__ImplementsAssignment_3_2_1 ) ) ;
    public final void rule__Interface__Group_3_2__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2651:1: ( ( ( rule__Interface__ImplementsAssignment_3_2_1 ) ) )
            // InternalMiniJava.g:2652:1: ( ( rule__Interface__ImplementsAssignment_3_2_1 ) )
            {
            // InternalMiniJava.g:2652:1: ( ( rule__Interface__ImplementsAssignment_3_2_1 ) )
            // InternalMiniJava.g:2653:2: ( rule__Interface__ImplementsAssignment_3_2_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getInterfaceAccess().getImplementsAssignment_3_2_1()); 
            }
            // InternalMiniJava.g:2654:2: ( rule__Interface__ImplementsAssignment_3_2_1 )
            // InternalMiniJava.g:2654:3: rule__Interface__ImplementsAssignment_3_2_1
            {
            pushFollow(FOLLOW_2);
            rule__Interface__ImplementsAssignment_3_2_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getInterfaceAccess().getImplementsAssignment_3_2_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__Group_3_2__1__Impl"


    // $ANTLR start "rule__Method__Group__0"
    // InternalMiniJava.g:2663:1: rule__Method__Group__0 : rule__Method__Group__0__Impl rule__Method__Group__1 ;
    public final void rule__Method__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2667:1: ( rule__Method__Group__0__Impl rule__Method__Group__1 )
            // InternalMiniJava.g:2668:2: rule__Method__Group__0__Impl rule__Method__Group__1
            {
            pushFollow(FOLLOW_19);
            rule__Method__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Method__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group__0"


    // $ANTLR start "rule__Method__Group__0__Impl"
    // InternalMiniJava.g:2675:1: rule__Method__Group__0__Impl : ( ( rule__Method__AccessAssignment_0 )? ) ;
    public final void rule__Method__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2679:1: ( ( ( rule__Method__AccessAssignment_0 )? ) )
            // InternalMiniJava.g:2680:1: ( ( rule__Method__AccessAssignment_0 )? )
            {
            // InternalMiniJava.g:2680:1: ( ( rule__Method__AccessAssignment_0 )? )
            // InternalMiniJava.g:2681:2: ( rule__Method__AccessAssignment_0 )?
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getAccessAssignment_0()); 
            }
            // InternalMiniJava.g:2682:2: ( rule__Method__AccessAssignment_0 )?
            int alt33=2;
            int LA33_0 = input.LA(1);

            if ( ((LA33_0>=14 && LA33_0<=16)) ) {
                alt33=1;
            }
            switch (alt33) {
                case 1 :
                    // InternalMiniJava.g:2682:3: rule__Method__AccessAssignment_0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Method__AccessAssignment_0();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getAccessAssignment_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group__0__Impl"


    // $ANTLR start "rule__Method__Group__1"
    // InternalMiniJava.g:2690:1: rule__Method__Group__1 : rule__Method__Group__1__Impl rule__Method__Group__2 ;
    public final void rule__Method__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2694:1: ( rule__Method__Group__1__Impl rule__Method__Group__2 )
            // InternalMiniJava.g:2695:2: rule__Method__Group__1__Impl rule__Method__Group__2
            {
            pushFollow(FOLLOW_19);
            rule__Method__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Method__Group__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group__1"


    // $ANTLR start "rule__Method__Group__1__Impl"
    // InternalMiniJava.g:2702:1: rule__Method__Group__1__Impl : ( ( rule__Method__AbstractAssignment_1 )? ) ;
    public final void rule__Method__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2706:1: ( ( ( rule__Method__AbstractAssignment_1 )? ) )
            // InternalMiniJava.g:2707:1: ( ( rule__Method__AbstractAssignment_1 )? )
            {
            // InternalMiniJava.g:2707:1: ( ( rule__Method__AbstractAssignment_1 )? )
            // InternalMiniJava.g:2708:2: ( rule__Method__AbstractAssignment_1 )?
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getAbstractAssignment_1()); 
            }
            // InternalMiniJava.g:2709:2: ( rule__Method__AbstractAssignment_1 )?
            int alt34=2;
            int LA34_0 = input.LA(1);

            if ( (LA34_0==63) ) {
                alt34=1;
            }
            switch (alt34) {
                case 1 :
                    // InternalMiniJava.g:2709:3: rule__Method__AbstractAssignment_1
                    {
                    pushFollow(FOLLOW_2);
                    rule__Method__AbstractAssignment_1();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getAbstractAssignment_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group__1__Impl"


    // $ANTLR start "rule__Method__Group__2"
    // InternalMiniJava.g:2717:1: rule__Method__Group__2 : rule__Method__Group__2__Impl rule__Method__Group__3 ;
    public final void rule__Method__Group__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2721:1: ( rule__Method__Group__2__Impl rule__Method__Group__3 )
            // InternalMiniJava.g:2722:2: rule__Method__Group__2__Impl rule__Method__Group__3
            {
            pushFollow(FOLLOW_19);
            rule__Method__Group__2__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Method__Group__3();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group__2"


    // $ANTLR start "rule__Method__Group__2__Impl"
    // InternalMiniJava.g:2729:1: rule__Method__Group__2__Impl : ( ( rule__Method__StaticAssignment_2 )? ) ;
    public final void rule__Method__Group__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2733:1: ( ( ( rule__Method__StaticAssignment_2 )? ) )
            // InternalMiniJava.g:2734:1: ( ( rule__Method__StaticAssignment_2 )? )
            {
            // InternalMiniJava.g:2734:1: ( ( rule__Method__StaticAssignment_2 )? )
            // InternalMiniJava.g:2735:2: ( rule__Method__StaticAssignment_2 )?
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getStaticAssignment_2()); 
            }
            // InternalMiniJava.g:2736:2: ( rule__Method__StaticAssignment_2 )?
            int alt35=2;
            int LA35_0 = input.LA(1);

            if ( (LA35_0==64) ) {
                alt35=1;
            }
            switch (alt35) {
                case 1 :
                    // InternalMiniJava.g:2736:3: rule__Method__StaticAssignment_2
                    {
                    pushFollow(FOLLOW_2);
                    rule__Method__StaticAssignment_2();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getStaticAssignment_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group__2__Impl"


    // $ANTLR start "rule__Method__Group__3"
    // InternalMiniJava.g:2744:1: rule__Method__Group__3 : rule__Method__Group__3__Impl rule__Method__Group__4 ;
    public final void rule__Method__Group__3() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2748:1: ( rule__Method__Group__3__Impl rule__Method__Group__4 )
            // InternalMiniJava.g:2749:2: rule__Method__Group__3__Impl rule__Method__Group__4
            {
            pushFollow(FOLLOW_20);
            rule__Method__Group__3__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Method__Group__4();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group__3"


    // $ANTLR start "rule__Method__Group__3__Impl"
    // InternalMiniJava.g:2756:1: rule__Method__Group__3__Impl : ( ( rule__Method__TypeRefAssignment_3 ) ) ;
    public final void rule__Method__Group__3__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2760:1: ( ( ( rule__Method__TypeRefAssignment_3 ) ) )
            // InternalMiniJava.g:2761:1: ( ( rule__Method__TypeRefAssignment_3 ) )
            {
            // InternalMiniJava.g:2761:1: ( ( rule__Method__TypeRefAssignment_3 ) )
            // InternalMiniJava.g:2762:2: ( rule__Method__TypeRefAssignment_3 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getTypeRefAssignment_3()); 
            }
            // InternalMiniJava.g:2763:2: ( rule__Method__TypeRefAssignment_3 )
            // InternalMiniJava.g:2763:3: rule__Method__TypeRefAssignment_3
            {
            pushFollow(FOLLOW_2);
            rule__Method__TypeRefAssignment_3();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getTypeRefAssignment_3()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group__3__Impl"


    // $ANTLR start "rule__Method__Group__4"
    // InternalMiniJava.g:2771:1: rule__Method__Group__4 : rule__Method__Group__4__Impl rule__Method__Group__5 ;
    public final void rule__Method__Group__4() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2775:1: ( rule__Method__Group__4__Impl rule__Method__Group__5 )
            // InternalMiniJava.g:2776:2: rule__Method__Group__4__Impl rule__Method__Group__5
            {
            pushFollow(FOLLOW_20);
            rule__Method__Group__4__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Method__Group__5();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group__4"


    // $ANTLR start "rule__Method__Group__4__Impl"
    // InternalMiniJava.g:2783:1: rule__Method__Group__4__Impl : ( ( rule__Method__NameAssignment_4 )? ) ;
    public final void rule__Method__Group__4__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2787:1: ( ( ( rule__Method__NameAssignment_4 )? ) )
            // InternalMiniJava.g:2788:1: ( ( rule__Method__NameAssignment_4 )? )
            {
            // InternalMiniJava.g:2788:1: ( ( rule__Method__NameAssignment_4 )? )
            // InternalMiniJava.g:2789:2: ( rule__Method__NameAssignment_4 )?
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getNameAssignment_4()); 
            }
            // InternalMiniJava.g:2790:2: ( rule__Method__NameAssignment_4 )?
            int alt36=2;
            int LA36_0 = input.LA(1);

            if ( (LA36_0==RULE_ID) ) {
                alt36=1;
            }
            switch (alt36) {
                case 1 :
                    // InternalMiniJava.g:2790:3: rule__Method__NameAssignment_4
                    {
                    pushFollow(FOLLOW_2);
                    rule__Method__NameAssignment_4();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getNameAssignment_4()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group__4__Impl"


    // $ANTLR start "rule__Method__Group__5"
    // InternalMiniJava.g:2798:1: rule__Method__Group__5 : rule__Method__Group__5__Impl rule__Method__Group__6 ;
    public final void rule__Method__Group__5() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2802:1: ( rule__Method__Group__5__Impl rule__Method__Group__6 )
            // InternalMiniJava.g:2803:2: rule__Method__Group__5__Impl rule__Method__Group__6
            {
            pushFollow(FOLLOW_21);
            rule__Method__Group__5__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Method__Group__6();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group__5"


    // $ANTLR start "rule__Method__Group__5__Impl"
    // InternalMiniJava.g:2810:1: rule__Method__Group__5__Impl : ( '(' ) ;
    public final void rule__Method__Group__5__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2814:1: ( ( '(' ) )
            // InternalMiniJava.g:2815:1: ( '(' )
            {
            // InternalMiniJava.g:2815:1: ( '(' )
            // InternalMiniJava.g:2816:2: '('
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getLeftParenthesisKeyword_5()); 
            }
            match(input,28,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getLeftParenthesisKeyword_5()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group__5__Impl"


    // $ANTLR start "rule__Method__Group__6"
    // InternalMiniJava.g:2825:1: rule__Method__Group__6 : rule__Method__Group__6__Impl rule__Method__Group__7 ;
    public final void rule__Method__Group__6() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2829:1: ( rule__Method__Group__6__Impl rule__Method__Group__7 )
            // InternalMiniJava.g:2830:2: rule__Method__Group__6__Impl rule__Method__Group__7
            {
            pushFollow(FOLLOW_21);
            rule__Method__Group__6__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Method__Group__7();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group__6"


    // $ANTLR start "rule__Method__Group__6__Impl"
    // InternalMiniJava.g:2837:1: rule__Method__Group__6__Impl : ( ( rule__Method__Group_6__0 )? ) ;
    public final void rule__Method__Group__6__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2841:1: ( ( ( rule__Method__Group_6__0 )? ) )
            // InternalMiniJava.g:2842:1: ( ( rule__Method__Group_6__0 )? )
            {
            // InternalMiniJava.g:2842:1: ( ( rule__Method__Group_6__0 )? )
            // InternalMiniJava.g:2843:2: ( rule__Method__Group_6__0 )?
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getGroup_6()); 
            }
            // InternalMiniJava.g:2844:2: ( rule__Method__Group_6__0 )?
            int alt37=2;
            int LA37_0 = input.LA(1);

            if ( (LA37_0==RULE_ID||(LA37_0>=41 && LA37_0<=44)) ) {
                alt37=1;
            }
            switch (alt37) {
                case 1 :
                    // InternalMiniJava.g:2844:3: rule__Method__Group_6__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Method__Group_6__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getGroup_6()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group__6__Impl"


    // $ANTLR start "rule__Method__Group__7"
    // InternalMiniJava.g:2852:1: rule__Method__Group__7 : rule__Method__Group__7__Impl rule__Method__Group__8 ;
    public final void rule__Method__Group__7() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2856:1: ( rule__Method__Group__7__Impl rule__Method__Group__8 )
            // InternalMiniJava.g:2857:2: rule__Method__Group__7__Impl rule__Method__Group__8
            {
            pushFollow(FOLLOW_22);
            rule__Method__Group__7__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Method__Group__8();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group__7"


    // $ANTLR start "rule__Method__Group__7__Impl"
    // InternalMiniJava.g:2864:1: rule__Method__Group__7__Impl : ( ')' ) ;
    public final void rule__Method__Group__7__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2868:1: ( ( ')' ) )
            // InternalMiniJava.g:2869:1: ( ')' )
            {
            // InternalMiniJava.g:2869:1: ( ')' )
            // InternalMiniJava.g:2870:2: ')'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getRightParenthesisKeyword_7()); 
            }
            match(input,29,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getRightParenthesisKeyword_7()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group__7__Impl"


    // $ANTLR start "rule__Method__Group__8"
    // InternalMiniJava.g:2879:1: rule__Method__Group__8 : rule__Method__Group__8__Impl ;
    public final void rule__Method__Group__8() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2883:1: ( rule__Method__Group__8__Impl )
            // InternalMiniJava.g:2884:2: rule__Method__Group__8__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Method__Group__8__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group__8"


    // $ANTLR start "rule__Method__Group__8__Impl"
    // InternalMiniJava.g:2890:1: rule__Method__Group__8__Impl : ( ( rule__Method__Alternatives_8 ) ) ;
    public final void rule__Method__Group__8__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2894:1: ( ( ( rule__Method__Alternatives_8 ) ) )
            // InternalMiniJava.g:2895:1: ( ( rule__Method__Alternatives_8 ) )
            {
            // InternalMiniJava.g:2895:1: ( ( rule__Method__Alternatives_8 ) )
            // InternalMiniJava.g:2896:2: ( rule__Method__Alternatives_8 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getAlternatives_8()); 
            }
            // InternalMiniJava.g:2897:2: ( rule__Method__Alternatives_8 )
            // InternalMiniJava.g:2897:3: rule__Method__Alternatives_8
            {
            pushFollow(FOLLOW_2);
            rule__Method__Alternatives_8();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getAlternatives_8()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group__8__Impl"


    // $ANTLR start "rule__Method__Group_6__0"
    // InternalMiniJava.g:2906:1: rule__Method__Group_6__0 : rule__Method__Group_6__0__Impl rule__Method__Group_6__1 ;
    public final void rule__Method__Group_6__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2910:1: ( rule__Method__Group_6__0__Impl rule__Method__Group_6__1 )
            // InternalMiniJava.g:2911:2: rule__Method__Group_6__0__Impl rule__Method__Group_6__1
            {
            pushFollow(FOLLOW_15);
            rule__Method__Group_6__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Method__Group_6__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group_6__0"


    // $ANTLR start "rule__Method__Group_6__0__Impl"
    // InternalMiniJava.g:2918:1: rule__Method__Group_6__0__Impl : ( ( rule__Method__ParamsAssignment_6_0 ) ) ;
    public final void rule__Method__Group_6__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2922:1: ( ( ( rule__Method__ParamsAssignment_6_0 ) ) )
            // InternalMiniJava.g:2923:1: ( ( rule__Method__ParamsAssignment_6_0 ) )
            {
            // InternalMiniJava.g:2923:1: ( ( rule__Method__ParamsAssignment_6_0 ) )
            // InternalMiniJava.g:2924:2: ( rule__Method__ParamsAssignment_6_0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getParamsAssignment_6_0()); 
            }
            // InternalMiniJava.g:2925:2: ( rule__Method__ParamsAssignment_6_0 )
            // InternalMiniJava.g:2925:3: rule__Method__ParamsAssignment_6_0
            {
            pushFollow(FOLLOW_2);
            rule__Method__ParamsAssignment_6_0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getParamsAssignment_6_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group_6__0__Impl"


    // $ANTLR start "rule__Method__Group_6__1"
    // InternalMiniJava.g:2933:1: rule__Method__Group_6__1 : rule__Method__Group_6__1__Impl ;
    public final void rule__Method__Group_6__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2937:1: ( rule__Method__Group_6__1__Impl )
            // InternalMiniJava.g:2938:2: rule__Method__Group_6__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Method__Group_6__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group_6__1"


    // $ANTLR start "rule__Method__Group_6__1__Impl"
    // InternalMiniJava.g:2944:1: rule__Method__Group_6__1__Impl : ( ( rule__Method__Group_6_1__0 )* ) ;
    public final void rule__Method__Group_6__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2948:1: ( ( ( rule__Method__Group_6_1__0 )* ) )
            // InternalMiniJava.g:2949:1: ( ( rule__Method__Group_6_1__0 )* )
            {
            // InternalMiniJava.g:2949:1: ( ( rule__Method__Group_6_1__0 )* )
            // InternalMiniJava.g:2950:2: ( rule__Method__Group_6_1__0 )*
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getGroup_6_1()); 
            }
            // InternalMiniJava.g:2951:2: ( rule__Method__Group_6_1__0 )*
            loop38:
            do {
                int alt38=2;
                int LA38_0 = input.LA(1);

                if ( (LA38_0==26) ) {
                    alt38=1;
                }


                switch (alt38) {
            	case 1 :
            	    // InternalMiniJava.g:2951:3: rule__Method__Group_6_1__0
            	    {
            	    pushFollow(FOLLOW_16);
            	    rule__Method__Group_6_1__0();

            	    state._fsp--;
            	    if (state.failed) return ;

            	    }
            	    break;

            	default :
            	    break loop38;
                }
            } while (true);

            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getGroup_6_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group_6__1__Impl"


    // $ANTLR start "rule__Method__Group_6_1__0"
    // InternalMiniJava.g:2960:1: rule__Method__Group_6_1__0 : rule__Method__Group_6_1__0__Impl rule__Method__Group_6_1__1 ;
    public final void rule__Method__Group_6_1__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2964:1: ( rule__Method__Group_6_1__0__Impl rule__Method__Group_6_1__1 )
            // InternalMiniJava.g:2965:2: rule__Method__Group_6_1__0__Impl rule__Method__Group_6_1__1
            {
            pushFollow(FOLLOW_23);
            rule__Method__Group_6_1__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Method__Group_6_1__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group_6_1__0"


    // $ANTLR start "rule__Method__Group_6_1__0__Impl"
    // InternalMiniJava.g:2972:1: rule__Method__Group_6_1__0__Impl : ( ',' ) ;
    public final void rule__Method__Group_6_1__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2976:1: ( ( ',' ) )
            // InternalMiniJava.g:2977:1: ( ',' )
            {
            // InternalMiniJava.g:2977:1: ( ',' )
            // InternalMiniJava.g:2978:2: ','
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getCommaKeyword_6_1_0()); 
            }
            match(input,26,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getCommaKeyword_6_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group_6_1__0__Impl"


    // $ANTLR start "rule__Method__Group_6_1__1"
    // InternalMiniJava.g:2987:1: rule__Method__Group_6_1__1 : rule__Method__Group_6_1__1__Impl ;
    public final void rule__Method__Group_6_1__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:2991:1: ( rule__Method__Group_6_1__1__Impl )
            // InternalMiniJava.g:2992:2: rule__Method__Group_6_1__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Method__Group_6_1__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group_6_1__1"


    // $ANTLR start "rule__Method__Group_6_1__1__Impl"
    // InternalMiniJava.g:2998:1: rule__Method__Group_6_1__1__Impl : ( ( rule__Method__ParamsAssignment_6_1_1 ) ) ;
    public final void rule__Method__Group_6_1__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3002:1: ( ( ( rule__Method__ParamsAssignment_6_1_1 ) ) )
            // InternalMiniJava.g:3003:1: ( ( rule__Method__ParamsAssignment_6_1_1 ) )
            {
            // InternalMiniJava.g:3003:1: ( ( rule__Method__ParamsAssignment_6_1_1 ) )
            // InternalMiniJava.g:3004:2: ( rule__Method__ParamsAssignment_6_1_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getParamsAssignment_6_1_1()); 
            }
            // InternalMiniJava.g:3005:2: ( rule__Method__ParamsAssignment_6_1_1 )
            // InternalMiniJava.g:3005:3: rule__Method__ParamsAssignment_6_1_1
            {
            pushFollow(FOLLOW_2);
            rule__Method__ParamsAssignment_6_1_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getParamsAssignment_6_1_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__Group_6_1__1__Impl"


    // $ANTLR start "rule__Parameter__Group__0"
    // InternalMiniJava.g:3014:1: rule__Parameter__Group__0 : rule__Parameter__Group__0__Impl rule__Parameter__Group__1 ;
    public final void rule__Parameter__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3018:1: ( rule__Parameter__Group__0__Impl rule__Parameter__Group__1 )
            // InternalMiniJava.g:3019:2: rule__Parameter__Group__0__Impl rule__Parameter__Group__1
            {
            pushFollow(FOLLOW_6);
            rule__Parameter__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Parameter__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Parameter__Group__0"


    // $ANTLR start "rule__Parameter__Group__0__Impl"
    // InternalMiniJava.g:3026:1: rule__Parameter__Group__0__Impl : ( ( rule__Parameter__TypeRefAssignment_0 ) ) ;
    public final void rule__Parameter__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3030:1: ( ( ( rule__Parameter__TypeRefAssignment_0 ) ) )
            // InternalMiniJava.g:3031:1: ( ( rule__Parameter__TypeRefAssignment_0 ) )
            {
            // InternalMiniJava.g:3031:1: ( ( rule__Parameter__TypeRefAssignment_0 ) )
            // InternalMiniJava.g:3032:2: ( rule__Parameter__TypeRefAssignment_0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getParameterAccess().getTypeRefAssignment_0()); 
            }
            // InternalMiniJava.g:3033:2: ( rule__Parameter__TypeRefAssignment_0 )
            // InternalMiniJava.g:3033:3: rule__Parameter__TypeRefAssignment_0
            {
            pushFollow(FOLLOW_2);
            rule__Parameter__TypeRefAssignment_0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getParameterAccess().getTypeRefAssignment_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Parameter__Group__0__Impl"


    // $ANTLR start "rule__Parameter__Group__1"
    // InternalMiniJava.g:3041:1: rule__Parameter__Group__1 : rule__Parameter__Group__1__Impl ;
    public final void rule__Parameter__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3045:1: ( rule__Parameter__Group__1__Impl )
            // InternalMiniJava.g:3046:2: rule__Parameter__Group__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Parameter__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Parameter__Group__1"


    // $ANTLR start "rule__Parameter__Group__1__Impl"
    // InternalMiniJava.g:3052:1: rule__Parameter__Group__1__Impl : ( ( rule__Parameter__NameAssignment_1 ) ) ;
    public final void rule__Parameter__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3056:1: ( ( ( rule__Parameter__NameAssignment_1 ) ) )
            // InternalMiniJava.g:3057:1: ( ( rule__Parameter__NameAssignment_1 ) )
            {
            // InternalMiniJava.g:3057:1: ( ( rule__Parameter__NameAssignment_1 ) )
            // InternalMiniJava.g:3058:2: ( rule__Parameter__NameAssignment_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getParameterAccess().getNameAssignment_1()); 
            }
            // InternalMiniJava.g:3059:2: ( rule__Parameter__NameAssignment_1 )
            // InternalMiniJava.g:3059:3: rule__Parameter__NameAssignment_1
            {
            pushFollow(FOLLOW_2);
            rule__Parameter__NameAssignment_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getParameterAccess().getNameAssignment_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Parameter__Group__1__Impl"


    // $ANTLR start "rule__Field__Group__0"
    // InternalMiniJava.g:3068:1: rule__Field__Group__0 : rule__Field__Group__0__Impl rule__Field__Group__1 ;
    public final void rule__Field__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3072:1: ( rule__Field__Group__0__Impl rule__Field__Group__1 )
            // InternalMiniJava.g:3073:2: rule__Field__Group__0__Impl rule__Field__Group__1
            {
            pushFollow(FOLLOW_23);
            rule__Field__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Field__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Field__Group__0"


    // $ANTLR start "rule__Field__Group__0__Impl"
    // InternalMiniJava.g:3080:1: rule__Field__Group__0__Impl : ( ( rule__Field__AccessAssignment_0 )? ) ;
    public final void rule__Field__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3084:1: ( ( ( rule__Field__AccessAssignment_0 )? ) )
            // InternalMiniJava.g:3085:1: ( ( rule__Field__AccessAssignment_0 )? )
            {
            // InternalMiniJava.g:3085:1: ( ( rule__Field__AccessAssignment_0 )? )
            // InternalMiniJava.g:3086:2: ( rule__Field__AccessAssignment_0 )?
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getFieldAccess().getAccessAssignment_0()); 
            }
            // InternalMiniJava.g:3087:2: ( rule__Field__AccessAssignment_0 )?
            int alt39=2;
            int LA39_0 = input.LA(1);

            if ( ((LA39_0>=14 && LA39_0<=16)) ) {
                alt39=1;
            }
            switch (alt39) {
                case 1 :
                    // InternalMiniJava.g:3087:3: rule__Field__AccessAssignment_0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Field__AccessAssignment_0();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getFieldAccess().getAccessAssignment_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Field__Group__0__Impl"


    // $ANTLR start "rule__Field__Group__1"
    // InternalMiniJava.g:3095:1: rule__Field__Group__1 : rule__Field__Group__1__Impl rule__Field__Group__2 ;
    public final void rule__Field__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3099:1: ( rule__Field__Group__1__Impl rule__Field__Group__2 )
            // InternalMiniJava.g:3100:2: rule__Field__Group__1__Impl rule__Field__Group__2
            {
            pushFollow(FOLLOW_6);
            rule__Field__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Field__Group__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Field__Group__1"


    // $ANTLR start "rule__Field__Group__1__Impl"
    // InternalMiniJava.g:3107:1: rule__Field__Group__1__Impl : ( ( rule__Field__TypeRefAssignment_1 ) ) ;
    public final void rule__Field__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3111:1: ( ( ( rule__Field__TypeRefAssignment_1 ) ) )
            // InternalMiniJava.g:3112:1: ( ( rule__Field__TypeRefAssignment_1 ) )
            {
            // InternalMiniJava.g:3112:1: ( ( rule__Field__TypeRefAssignment_1 ) )
            // InternalMiniJava.g:3113:2: ( rule__Field__TypeRefAssignment_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getFieldAccess().getTypeRefAssignment_1()); 
            }
            // InternalMiniJava.g:3114:2: ( rule__Field__TypeRefAssignment_1 )
            // InternalMiniJava.g:3114:3: rule__Field__TypeRefAssignment_1
            {
            pushFollow(FOLLOW_2);
            rule__Field__TypeRefAssignment_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getFieldAccess().getTypeRefAssignment_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Field__Group__1__Impl"


    // $ANTLR start "rule__Field__Group__2"
    // InternalMiniJava.g:3122:1: rule__Field__Group__2 : rule__Field__Group__2__Impl rule__Field__Group__3 ;
    public final void rule__Field__Group__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3126:1: ( rule__Field__Group__2__Impl rule__Field__Group__3 )
            // InternalMiniJava.g:3127:2: rule__Field__Group__2__Impl rule__Field__Group__3
            {
            pushFollow(FOLLOW_24);
            rule__Field__Group__2__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Field__Group__3();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Field__Group__2"


    // $ANTLR start "rule__Field__Group__2__Impl"
    // InternalMiniJava.g:3134:1: rule__Field__Group__2__Impl : ( ( rule__Field__NameAssignment_2 ) ) ;
    public final void rule__Field__Group__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3138:1: ( ( ( rule__Field__NameAssignment_2 ) ) )
            // InternalMiniJava.g:3139:1: ( ( rule__Field__NameAssignment_2 ) )
            {
            // InternalMiniJava.g:3139:1: ( ( rule__Field__NameAssignment_2 ) )
            // InternalMiniJava.g:3140:2: ( rule__Field__NameAssignment_2 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getFieldAccess().getNameAssignment_2()); 
            }
            // InternalMiniJava.g:3141:2: ( rule__Field__NameAssignment_2 )
            // InternalMiniJava.g:3141:3: rule__Field__NameAssignment_2
            {
            pushFollow(FOLLOW_2);
            rule__Field__NameAssignment_2();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getFieldAccess().getNameAssignment_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Field__Group__2__Impl"


    // $ANTLR start "rule__Field__Group__3"
    // InternalMiniJava.g:3149:1: rule__Field__Group__3 : rule__Field__Group__3__Impl rule__Field__Group__4 ;
    public final void rule__Field__Group__3() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3153:1: ( rule__Field__Group__3__Impl rule__Field__Group__4 )
            // InternalMiniJava.g:3154:2: rule__Field__Group__3__Impl rule__Field__Group__4
            {
            pushFollow(FOLLOW_24);
            rule__Field__Group__3__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Field__Group__4();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Field__Group__3"


    // $ANTLR start "rule__Field__Group__3__Impl"
    // InternalMiniJava.g:3161:1: rule__Field__Group__3__Impl : ( ( rule__Field__Group_3__0 )? ) ;
    public final void rule__Field__Group__3__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3165:1: ( ( ( rule__Field__Group_3__0 )? ) )
            // InternalMiniJava.g:3166:1: ( ( rule__Field__Group_3__0 )? )
            {
            // InternalMiniJava.g:3166:1: ( ( rule__Field__Group_3__0 )? )
            // InternalMiniJava.g:3167:2: ( rule__Field__Group_3__0 )?
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getFieldAccess().getGroup_3()); 
            }
            // InternalMiniJava.g:3168:2: ( rule__Field__Group_3__0 )?
            int alt40=2;
            int LA40_0 = input.LA(1);

            if ( (LA40_0==30) ) {
                alt40=1;
            }
            switch (alt40) {
                case 1 :
                    // InternalMiniJava.g:3168:3: rule__Field__Group_3__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__Field__Group_3__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getFieldAccess().getGroup_3()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Field__Group__3__Impl"


    // $ANTLR start "rule__Field__Group__4"
    // InternalMiniJava.g:3176:1: rule__Field__Group__4 : rule__Field__Group__4__Impl ;
    public final void rule__Field__Group__4() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3180:1: ( rule__Field__Group__4__Impl )
            // InternalMiniJava.g:3181:2: rule__Field__Group__4__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Field__Group__4__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Field__Group__4"


    // $ANTLR start "rule__Field__Group__4__Impl"
    // InternalMiniJava.g:3187:1: rule__Field__Group__4__Impl : ( ';' ) ;
    public final void rule__Field__Group__4__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3191:1: ( ( ';' ) )
            // InternalMiniJava.g:3192:1: ( ';' )
            {
            // InternalMiniJava.g:3192:1: ( ';' )
            // InternalMiniJava.g:3193:2: ';'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getFieldAccess().getSemicolonKeyword_4()); 
            }
            match(input,11,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getFieldAccess().getSemicolonKeyword_4()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Field__Group__4__Impl"


    // $ANTLR start "rule__Field__Group_3__0"
    // InternalMiniJava.g:3203:1: rule__Field__Group_3__0 : rule__Field__Group_3__0__Impl rule__Field__Group_3__1 ;
    public final void rule__Field__Group_3__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3207:1: ( rule__Field__Group_3__0__Impl rule__Field__Group_3__1 )
            // InternalMiniJava.g:3208:2: rule__Field__Group_3__0__Impl rule__Field__Group_3__1
            {
            pushFollow(FOLLOW_25);
            rule__Field__Group_3__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Field__Group_3__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Field__Group_3__0"


    // $ANTLR start "rule__Field__Group_3__0__Impl"
    // InternalMiniJava.g:3215:1: rule__Field__Group_3__0__Impl : ( '=' ) ;
    public final void rule__Field__Group_3__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3219:1: ( ( '=' ) )
            // InternalMiniJava.g:3220:1: ( '=' )
            {
            // InternalMiniJava.g:3220:1: ( '=' )
            // InternalMiniJava.g:3221:2: '='
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getFieldAccess().getEqualsSignKeyword_3_0()); 
            }
            match(input,30,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getFieldAccess().getEqualsSignKeyword_3_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Field__Group_3__0__Impl"


    // $ANTLR start "rule__Field__Group_3__1"
    // InternalMiniJava.g:3230:1: rule__Field__Group_3__1 : rule__Field__Group_3__1__Impl ;
    public final void rule__Field__Group_3__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3234:1: ( rule__Field__Group_3__1__Impl )
            // InternalMiniJava.g:3235:2: rule__Field__Group_3__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Field__Group_3__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Field__Group_3__1"


    // $ANTLR start "rule__Field__Group_3__1__Impl"
    // InternalMiniJava.g:3241:1: rule__Field__Group_3__1__Impl : ( ( rule__Field__DefaultValueAssignment_3_1 ) ) ;
    public final void rule__Field__Group_3__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3245:1: ( ( ( rule__Field__DefaultValueAssignment_3_1 ) ) )
            // InternalMiniJava.g:3246:1: ( ( rule__Field__DefaultValueAssignment_3_1 ) )
            {
            // InternalMiniJava.g:3246:1: ( ( rule__Field__DefaultValueAssignment_3_1 ) )
            // InternalMiniJava.g:3247:2: ( rule__Field__DefaultValueAssignment_3_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getFieldAccess().getDefaultValueAssignment_3_1()); 
            }
            // InternalMiniJava.g:3248:2: ( rule__Field__DefaultValueAssignment_3_1 )
            // InternalMiniJava.g:3248:3: rule__Field__DefaultValueAssignment_3_1
            {
            pushFollow(FOLLOW_2);
            rule__Field__DefaultValueAssignment_3_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getFieldAccess().getDefaultValueAssignment_3_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Field__Group_3__1__Impl"


    // $ANTLR start "rule__Block__Group__0"
    // InternalMiniJava.g:3257:1: rule__Block__Group__0 : rule__Block__Group__0__Impl rule__Block__Group__1 ;
    public final void rule__Block__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3261:1: ( rule__Block__Group__0__Impl rule__Block__Group__1 )
            // InternalMiniJava.g:3262:2: rule__Block__Group__0__Impl rule__Block__Group__1
            {
            pushFollow(FOLLOW_26);
            rule__Block__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Block__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Block__Group__0"


    // $ANTLR start "rule__Block__Group__0__Impl"
    // InternalMiniJava.g:3269:1: rule__Block__Group__0__Impl : ( () ) ;
    public final void rule__Block__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3273:1: ( ( () ) )
            // InternalMiniJava.g:3274:1: ( () )
            {
            // InternalMiniJava.g:3274:1: ( () )
            // InternalMiniJava.g:3275:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getBlockAccess().getBlockAction_0()); 
            }
            // InternalMiniJava.g:3276:2: ()
            // InternalMiniJava.g:3276:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getBlockAccess().getBlockAction_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Block__Group__0__Impl"


    // $ANTLR start "rule__Block__Group__1"
    // InternalMiniJava.g:3284:1: rule__Block__Group__1 : rule__Block__Group__1__Impl rule__Block__Group__2 ;
    public final void rule__Block__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3288:1: ( rule__Block__Group__1__Impl rule__Block__Group__2 )
            // InternalMiniJava.g:3289:2: rule__Block__Group__1__Impl rule__Block__Group__2
            {
            pushFollow(FOLLOW_27);
            rule__Block__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Block__Group__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Block__Group__1"


    // $ANTLR start "rule__Block__Group__1__Impl"
    // InternalMiniJava.g:3296:1: rule__Block__Group__1__Impl : ( '{' ) ;
    public final void rule__Block__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3300:1: ( ( '{' ) )
            // InternalMiniJava.g:3301:1: ( '{' )
            {
            // InternalMiniJava.g:3301:1: ( '{' )
            // InternalMiniJava.g:3302:2: '{'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getBlockAccess().getLeftCurlyBracketKeyword_1()); 
            }
            match(input,22,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getBlockAccess().getLeftCurlyBracketKeyword_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Block__Group__1__Impl"


    // $ANTLR start "rule__Block__Group__2"
    // InternalMiniJava.g:3311:1: rule__Block__Group__2 : rule__Block__Group__2__Impl rule__Block__Group__3 ;
    public final void rule__Block__Group__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3315:1: ( rule__Block__Group__2__Impl rule__Block__Group__3 )
            // InternalMiniJava.g:3316:2: rule__Block__Group__2__Impl rule__Block__Group__3
            {
            pushFollow(FOLLOW_27);
            rule__Block__Group__2__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Block__Group__3();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Block__Group__2"


    // $ANTLR start "rule__Block__Group__2__Impl"
    // InternalMiniJava.g:3323:1: rule__Block__Group__2__Impl : ( ( rule__Block__StatementsAssignment_2 )* ) ;
    public final void rule__Block__Group__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3327:1: ( ( ( rule__Block__StatementsAssignment_2 )* ) )
            // InternalMiniJava.g:3328:1: ( ( rule__Block__StatementsAssignment_2 )* )
            {
            // InternalMiniJava.g:3328:1: ( ( rule__Block__StatementsAssignment_2 )* )
            // InternalMiniJava.g:3329:2: ( rule__Block__StatementsAssignment_2 )*
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getBlockAccess().getStatementsAssignment_2()); 
            }
            // InternalMiniJava.g:3330:2: ( rule__Block__StatementsAssignment_2 )*
            loop41:
            do {
                int alt41=2;
                int LA41_0 = input.LA(1);

                if ( ((LA41_0>=RULE_ID && LA41_0<=RULE_INT)||(LA41_0>=12 && LA41_0<=13)||LA41_0==22||LA41_0==28||LA41_0==31||(LA41_0>=34 && LA41_0<=35)||(LA41_0>=37 && LA41_0<=38)||(LA41_0>=41 && LA41_0<=44)||LA41_0==54||(LA41_0>=58 && LA41_0<=62)) ) {
                    alt41=1;
                }


                switch (alt41) {
            	case 1 :
            	    // InternalMiniJava.g:3330:3: rule__Block__StatementsAssignment_2
            	    {
            	    pushFollow(FOLLOW_28);
            	    rule__Block__StatementsAssignment_2();

            	    state._fsp--;
            	    if (state.failed) return ;

            	    }
            	    break;

            	default :
            	    break loop41;
                }
            } while (true);

            if ( state.backtracking==0 ) {
               after(grammarAccess.getBlockAccess().getStatementsAssignment_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Block__Group__2__Impl"


    // $ANTLR start "rule__Block__Group__3"
    // InternalMiniJava.g:3338:1: rule__Block__Group__3 : rule__Block__Group__3__Impl ;
    public final void rule__Block__Group__3() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3342:1: ( rule__Block__Group__3__Impl )
            // InternalMiniJava.g:3343:2: rule__Block__Group__3__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Block__Group__3__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Block__Group__3"


    // $ANTLR start "rule__Block__Group__3__Impl"
    // InternalMiniJava.g:3349:1: rule__Block__Group__3__Impl : ( '}' ) ;
    public final void rule__Block__Group__3__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3353:1: ( ( '}' ) )
            // InternalMiniJava.g:3354:1: ( '}' )
            {
            // InternalMiniJava.g:3354:1: ( '}' )
            // InternalMiniJava.g:3355:2: '}'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getBlockAccess().getRightCurlyBracketKeyword_3()); 
            }
            match(input,23,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getBlockAccess().getRightCurlyBracketKeyword_3()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Block__Group__3__Impl"


    // $ANTLR start "rule__Statement__Group_0__0"
    // InternalMiniJava.g:3365:1: rule__Statement__Group_0__0 : rule__Statement__Group_0__0__Impl rule__Statement__Group_0__1 ;
    public final void rule__Statement__Group_0__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3369:1: ( rule__Statement__Group_0__0__Impl rule__Statement__Group_0__1 )
            // InternalMiniJava.g:3370:2: rule__Statement__Group_0__0__Impl rule__Statement__Group_0__1
            {
            pushFollow(FOLLOW_7);
            rule__Statement__Group_0__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Statement__Group_0__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Statement__Group_0__0"


    // $ANTLR start "rule__Statement__Group_0__0__Impl"
    // InternalMiniJava.g:3377:1: rule__Statement__Group_0__0__Impl : ( ruleReturn ) ;
    public final void rule__Statement__Group_0__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3381:1: ( ( ruleReturn ) )
            // InternalMiniJava.g:3382:1: ( ruleReturn )
            {
            // InternalMiniJava.g:3382:1: ( ruleReturn )
            // InternalMiniJava.g:3383:2: ruleReturn
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getStatementAccess().getReturnParserRuleCall_0_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleReturn();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getStatementAccess().getReturnParserRuleCall_0_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Statement__Group_0__0__Impl"


    // $ANTLR start "rule__Statement__Group_0__1"
    // InternalMiniJava.g:3392:1: rule__Statement__Group_0__1 : rule__Statement__Group_0__1__Impl ;
    public final void rule__Statement__Group_0__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3396:1: ( rule__Statement__Group_0__1__Impl )
            // InternalMiniJava.g:3397:2: rule__Statement__Group_0__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Statement__Group_0__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Statement__Group_0__1"


    // $ANTLR start "rule__Statement__Group_0__1__Impl"
    // InternalMiniJava.g:3403:1: rule__Statement__Group_0__1__Impl : ( ';' ) ;
    public final void rule__Statement__Group_0__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3407:1: ( ( ';' ) )
            // InternalMiniJava.g:3408:1: ( ';' )
            {
            // InternalMiniJava.g:3408:1: ( ';' )
            // InternalMiniJava.g:3409:2: ';'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getStatementAccess().getSemicolonKeyword_0_1()); 
            }
            match(input,11,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getStatementAccess().getSemicolonKeyword_0_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Statement__Group_0__1__Impl"


    // $ANTLR start "rule__Statement__Group_1__0"
    // InternalMiniJava.g:3419:1: rule__Statement__Group_1__0 : rule__Statement__Group_1__0__Impl rule__Statement__Group_1__1 ;
    public final void rule__Statement__Group_1__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3423:1: ( rule__Statement__Group_1__0__Impl rule__Statement__Group_1__1 )
            // InternalMiniJava.g:3424:2: rule__Statement__Group_1__0__Impl rule__Statement__Group_1__1
            {
            pushFollow(FOLLOW_7);
            rule__Statement__Group_1__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Statement__Group_1__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Statement__Group_1__0"


    // $ANTLR start "rule__Statement__Group_1__0__Impl"
    // InternalMiniJava.g:3431:1: rule__Statement__Group_1__0__Impl : ( ( ruleAssignment ) ) ;
    public final void rule__Statement__Group_1__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3435:1: ( ( ( ruleAssignment ) ) )
            // InternalMiniJava.g:3436:1: ( ( ruleAssignment ) )
            {
            // InternalMiniJava.g:3436:1: ( ( ruleAssignment ) )
            // InternalMiniJava.g:3437:2: ( ruleAssignment )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getStatementAccess().getAssignmentParserRuleCall_1_0()); 
            }
            // InternalMiniJava.g:3438:2: ( ruleAssignment )
            // InternalMiniJava.g:3438:3: ruleAssignment
            {
            pushFollow(FOLLOW_2);
            ruleAssignment();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getStatementAccess().getAssignmentParserRuleCall_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Statement__Group_1__0__Impl"


    // $ANTLR start "rule__Statement__Group_1__1"
    // InternalMiniJava.g:3446:1: rule__Statement__Group_1__1 : rule__Statement__Group_1__1__Impl ;
    public final void rule__Statement__Group_1__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3450:1: ( rule__Statement__Group_1__1__Impl )
            // InternalMiniJava.g:3451:2: rule__Statement__Group_1__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Statement__Group_1__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Statement__Group_1__1"


    // $ANTLR start "rule__Statement__Group_1__1__Impl"
    // InternalMiniJava.g:3457:1: rule__Statement__Group_1__1__Impl : ( ';' ) ;
    public final void rule__Statement__Group_1__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3461:1: ( ( ';' ) )
            // InternalMiniJava.g:3462:1: ( ';' )
            {
            // InternalMiniJava.g:3462:1: ( ';' )
            // InternalMiniJava.g:3463:2: ';'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getStatementAccess().getSemicolonKeyword_1_1()); 
            }
            match(input,11,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getStatementAccess().getSemicolonKeyword_1_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Statement__Group_1__1__Impl"


    // $ANTLR start "rule__Statement__Group_5__0"
    // InternalMiniJava.g:3473:1: rule__Statement__Group_5__0 : rule__Statement__Group_5__0__Impl rule__Statement__Group_5__1 ;
    public final void rule__Statement__Group_5__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3477:1: ( rule__Statement__Group_5__0__Impl rule__Statement__Group_5__1 )
            // InternalMiniJava.g:3478:2: rule__Statement__Group_5__0__Impl rule__Statement__Group_5__1
            {
            pushFollow(FOLLOW_7);
            rule__Statement__Group_5__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Statement__Group_5__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Statement__Group_5__0"


    // $ANTLR start "rule__Statement__Group_5__0__Impl"
    // InternalMiniJava.g:3485:1: rule__Statement__Group_5__0__Impl : ( rulePrintStatement ) ;
    public final void rule__Statement__Group_5__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3489:1: ( ( rulePrintStatement ) )
            // InternalMiniJava.g:3490:1: ( rulePrintStatement )
            {
            // InternalMiniJava.g:3490:1: ( rulePrintStatement )
            // InternalMiniJava.g:3491:2: rulePrintStatement
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getStatementAccess().getPrintStatementParserRuleCall_5_0()); 
            }
            pushFollow(FOLLOW_2);
            rulePrintStatement();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getStatementAccess().getPrintStatementParserRuleCall_5_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Statement__Group_5__0__Impl"


    // $ANTLR start "rule__Statement__Group_5__1"
    // InternalMiniJava.g:3500:1: rule__Statement__Group_5__1 : rule__Statement__Group_5__1__Impl ;
    public final void rule__Statement__Group_5__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3504:1: ( rule__Statement__Group_5__1__Impl )
            // InternalMiniJava.g:3505:2: rule__Statement__Group_5__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Statement__Group_5__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Statement__Group_5__1"


    // $ANTLR start "rule__Statement__Group_5__1__Impl"
    // InternalMiniJava.g:3511:1: rule__Statement__Group_5__1__Impl : ( ';' ) ;
    public final void rule__Statement__Group_5__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3515:1: ( ( ';' ) )
            // InternalMiniJava.g:3516:1: ( ';' )
            {
            // InternalMiniJava.g:3516:1: ( ';' )
            // InternalMiniJava.g:3517:2: ';'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getStatementAccess().getSemicolonKeyword_5_1()); 
            }
            match(input,11,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getStatementAccess().getSemicolonKeyword_5_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Statement__Group_5__1__Impl"


    // $ANTLR start "rule__Statement__Group_7__0"
    // InternalMiniJava.g:3527:1: rule__Statement__Group_7__0 : rule__Statement__Group_7__0__Impl rule__Statement__Group_7__1 ;
    public final void rule__Statement__Group_7__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3531:1: ( rule__Statement__Group_7__0__Impl rule__Statement__Group_7__1 )
            // InternalMiniJava.g:3532:2: rule__Statement__Group_7__0__Impl rule__Statement__Group_7__1
            {
            pushFollow(FOLLOW_7);
            rule__Statement__Group_7__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Statement__Group_7__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Statement__Group_7__0"


    // $ANTLR start "rule__Statement__Group_7__0__Impl"
    // InternalMiniJava.g:3539:1: rule__Statement__Group_7__0__Impl : ( ruleSelectionExpression ) ;
    public final void rule__Statement__Group_7__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3543:1: ( ( ruleSelectionExpression ) )
            // InternalMiniJava.g:3544:1: ( ruleSelectionExpression )
            {
            // InternalMiniJava.g:3544:1: ( ruleSelectionExpression )
            // InternalMiniJava.g:3545:2: ruleSelectionExpression
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getStatementAccess().getSelectionExpressionParserRuleCall_7_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleSelectionExpression();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getStatementAccess().getSelectionExpressionParserRuleCall_7_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Statement__Group_7__0__Impl"


    // $ANTLR start "rule__Statement__Group_7__1"
    // InternalMiniJava.g:3554:1: rule__Statement__Group_7__1 : rule__Statement__Group_7__1__Impl ;
    public final void rule__Statement__Group_7__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3558:1: ( rule__Statement__Group_7__1__Impl )
            // InternalMiniJava.g:3559:2: rule__Statement__Group_7__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Statement__Group_7__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Statement__Group_7__1"


    // $ANTLR start "rule__Statement__Group_7__1__Impl"
    // InternalMiniJava.g:3565:1: rule__Statement__Group_7__1__Impl : ( ';' ) ;
    public final void rule__Statement__Group_7__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3569:1: ( ( ';' ) )
            // InternalMiniJava.g:3570:1: ( ';' )
            {
            // InternalMiniJava.g:3570:1: ( ';' )
            // InternalMiniJava.g:3571:2: ';'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getStatementAccess().getSemicolonKeyword_7_1()); 
            }
            match(input,11,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getStatementAccess().getSemicolonKeyword_7_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Statement__Group_7__1__Impl"


    // $ANTLR start "rule__PrintStatement__Group__0"
    // InternalMiniJava.g:3581:1: rule__PrintStatement__Group__0 : rule__PrintStatement__Group__0__Impl rule__PrintStatement__Group__1 ;
    public final void rule__PrintStatement__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3585:1: ( rule__PrintStatement__Group__0__Impl rule__PrintStatement__Group__1 )
            // InternalMiniJava.g:3586:2: rule__PrintStatement__Group__0__Impl rule__PrintStatement__Group__1
            {
            pushFollow(FOLLOW_8);
            rule__PrintStatement__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__PrintStatement__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PrintStatement__Group__0"


    // $ANTLR start "rule__PrintStatement__Group__0__Impl"
    // InternalMiniJava.g:3593:1: rule__PrintStatement__Group__0__Impl : ( 'System' ) ;
    public final void rule__PrintStatement__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3597:1: ( ( 'System' ) )
            // InternalMiniJava.g:3598:1: ( 'System' )
            {
            // InternalMiniJava.g:3598:1: ( 'System' )
            // InternalMiniJava.g:3599:2: 'System'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrintStatementAccess().getSystemKeyword_0()); 
            }
            match(input,31,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrintStatementAccess().getSystemKeyword_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PrintStatement__Group__0__Impl"


    // $ANTLR start "rule__PrintStatement__Group__1"
    // InternalMiniJava.g:3608:1: rule__PrintStatement__Group__1 : rule__PrintStatement__Group__1__Impl rule__PrintStatement__Group__2 ;
    public final void rule__PrintStatement__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3612:1: ( rule__PrintStatement__Group__1__Impl rule__PrintStatement__Group__2 )
            // InternalMiniJava.g:3613:2: rule__PrintStatement__Group__1__Impl rule__PrintStatement__Group__2
            {
            pushFollow(FOLLOW_29);
            rule__PrintStatement__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__PrintStatement__Group__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PrintStatement__Group__1"


    // $ANTLR start "rule__PrintStatement__Group__1__Impl"
    // InternalMiniJava.g:3620:1: rule__PrintStatement__Group__1__Impl : ( '.' ) ;
    public final void rule__PrintStatement__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3624:1: ( ( '.' ) )
            // InternalMiniJava.g:3625:1: ( '.' )
            {
            // InternalMiniJava.g:3625:1: ( '.' )
            // InternalMiniJava.g:3626:2: '.'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrintStatementAccess().getFullStopKeyword_1()); 
            }
            match(input,19,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrintStatementAccess().getFullStopKeyword_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PrintStatement__Group__1__Impl"


    // $ANTLR start "rule__PrintStatement__Group__2"
    // InternalMiniJava.g:3635:1: rule__PrintStatement__Group__2 : rule__PrintStatement__Group__2__Impl rule__PrintStatement__Group__3 ;
    public final void rule__PrintStatement__Group__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3639:1: ( rule__PrintStatement__Group__2__Impl rule__PrintStatement__Group__3 )
            // InternalMiniJava.g:3640:2: rule__PrintStatement__Group__2__Impl rule__PrintStatement__Group__3
            {
            pushFollow(FOLLOW_8);
            rule__PrintStatement__Group__2__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__PrintStatement__Group__3();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PrintStatement__Group__2"


    // $ANTLR start "rule__PrintStatement__Group__2__Impl"
    // InternalMiniJava.g:3647:1: rule__PrintStatement__Group__2__Impl : ( 'out' ) ;
    public final void rule__PrintStatement__Group__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3651:1: ( ( 'out' ) )
            // InternalMiniJava.g:3652:1: ( 'out' )
            {
            // InternalMiniJava.g:3652:1: ( 'out' )
            // InternalMiniJava.g:3653:2: 'out'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrintStatementAccess().getOutKeyword_2()); 
            }
            match(input,32,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrintStatementAccess().getOutKeyword_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PrintStatement__Group__2__Impl"


    // $ANTLR start "rule__PrintStatement__Group__3"
    // InternalMiniJava.g:3662:1: rule__PrintStatement__Group__3 : rule__PrintStatement__Group__3__Impl rule__PrintStatement__Group__4 ;
    public final void rule__PrintStatement__Group__3() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3666:1: ( rule__PrintStatement__Group__3__Impl rule__PrintStatement__Group__4 )
            // InternalMiniJava.g:3667:2: rule__PrintStatement__Group__3__Impl rule__PrintStatement__Group__4
            {
            pushFollow(FOLLOW_30);
            rule__PrintStatement__Group__3__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__PrintStatement__Group__4();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PrintStatement__Group__3"


    // $ANTLR start "rule__PrintStatement__Group__3__Impl"
    // InternalMiniJava.g:3674:1: rule__PrintStatement__Group__3__Impl : ( '.' ) ;
    public final void rule__PrintStatement__Group__3__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3678:1: ( ( '.' ) )
            // InternalMiniJava.g:3679:1: ( '.' )
            {
            // InternalMiniJava.g:3679:1: ( '.' )
            // InternalMiniJava.g:3680:2: '.'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrintStatementAccess().getFullStopKeyword_3()); 
            }
            match(input,19,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrintStatementAccess().getFullStopKeyword_3()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PrintStatement__Group__3__Impl"


    // $ANTLR start "rule__PrintStatement__Group__4"
    // InternalMiniJava.g:3689:1: rule__PrintStatement__Group__4 : rule__PrintStatement__Group__4__Impl rule__PrintStatement__Group__5 ;
    public final void rule__PrintStatement__Group__4() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3693:1: ( rule__PrintStatement__Group__4__Impl rule__PrintStatement__Group__5 )
            // InternalMiniJava.g:3694:2: rule__PrintStatement__Group__4__Impl rule__PrintStatement__Group__5
            {
            pushFollow(FOLLOW_31);
            rule__PrintStatement__Group__4__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__PrintStatement__Group__5();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PrintStatement__Group__4"


    // $ANTLR start "rule__PrintStatement__Group__4__Impl"
    // InternalMiniJava.g:3701:1: rule__PrintStatement__Group__4__Impl : ( 'println' ) ;
    public final void rule__PrintStatement__Group__4__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3705:1: ( ( 'println' ) )
            // InternalMiniJava.g:3706:1: ( 'println' )
            {
            // InternalMiniJava.g:3706:1: ( 'println' )
            // InternalMiniJava.g:3707:2: 'println'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrintStatementAccess().getPrintlnKeyword_4()); 
            }
            match(input,33,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrintStatementAccess().getPrintlnKeyword_4()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PrintStatement__Group__4__Impl"


    // $ANTLR start "rule__PrintStatement__Group__5"
    // InternalMiniJava.g:3716:1: rule__PrintStatement__Group__5 : rule__PrintStatement__Group__5__Impl rule__PrintStatement__Group__6 ;
    public final void rule__PrintStatement__Group__5() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3720:1: ( rule__PrintStatement__Group__5__Impl rule__PrintStatement__Group__6 )
            // InternalMiniJava.g:3721:2: rule__PrintStatement__Group__5__Impl rule__PrintStatement__Group__6
            {
            pushFollow(FOLLOW_25);
            rule__PrintStatement__Group__5__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__PrintStatement__Group__6();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PrintStatement__Group__5"


    // $ANTLR start "rule__PrintStatement__Group__5__Impl"
    // InternalMiniJava.g:3728:1: rule__PrintStatement__Group__5__Impl : ( '(' ) ;
    public final void rule__PrintStatement__Group__5__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3732:1: ( ( '(' ) )
            // InternalMiniJava.g:3733:1: ( '(' )
            {
            // InternalMiniJava.g:3733:1: ( '(' )
            // InternalMiniJava.g:3734:2: '('
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrintStatementAccess().getLeftParenthesisKeyword_5()); 
            }
            match(input,28,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrintStatementAccess().getLeftParenthesisKeyword_5()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PrintStatement__Group__5__Impl"


    // $ANTLR start "rule__PrintStatement__Group__6"
    // InternalMiniJava.g:3743:1: rule__PrintStatement__Group__6 : rule__PrintStatement__Group__6__Impl rule__PrintStatement__Group__7 ;
    public final void rule__PrintStatement__Group__6() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3747:1: ( rule__PrintStatement__Group__6__Impl rule__PrintStatement__Group__7 )
            // InternalMiniJava.g:3748:2: rule__PrintStatement__Group__6__Impl rule__PrintStatement__Group__7
            {
            pushFollow(FOLLOW_32);
            rule__PrintStatement__Group__6__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__PrintStatement__Group__7();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PrintStatement__Group__6"


    // $ANTLR start "rule__PrintStatement__Group__6__Impl"
    // InternalMiniJava.g:3755:1: rule__PrintStatement__Group__6__Impl : ( ( rule__PrintStatement__ExpressionAssignment_6 ) ) ;
    public final void rule__PrintStatement__Group__6__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3759:1: ( ( ( rule__PrintStatement__ExpressionAssignment_6 ) ) )
            // InternalMiniJava.g:3760:1: ( ( rule__PrintStatement__ExpressionAssignment_6 ) )
            {
            // InternalMiniJava.g:3760:1: ( ( rule__PrintStatement__ExpressionAssignment_6 ) )
            // InternalMiniJava.g:3761:2: ( rule__PrintStatement__ExpressionAssignment_6 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrintStatementAccess().getExpressionAssignment_6()); 
            }
            // InternalMiniJava.g:3762:2: ( rule__PrintStatement__ExpressionAssignment_6 )
            // InternalMiniJava.g:3762:3: rule__PrintStatement__ExpressionAssignment_6
            {
            pushFollow(FOLLOW_2);
            rule__PrintStatement__ExpressionAssignment_6();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrintStatementAccess().getExpressionAssignment_6()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PrintStatement__Group__6__Impl"


    // $ANTLR start "rule__PrintStatement__Group__7"
    // InternalMiniJava.g:3770:1: rule__PrintStatement__Group__7 : rule__PrintStatement__Group__7__Impl ;
    public final void rule__PrintStatement__Group__7() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3774:1: ( rule__PrintStatement__Group__7__Impl )
            // InternalMiniJava.g:3775:2: rule__PrintStatement__Group__7__Impl
            {
            pushFollow(FOLLOW_2);
            rule__PrintStatement__Group__7__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PrintStatement__Group__7"


    // $ANTLR start "rule__PrintStatement__Group__7__Impl"
    // InternalMiniJava.g:3781:1: rule__PrintStatement__Group__7__Impl : ( ')' ) ;
    public final void rule__PrintStatement__Group__7__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3785:1: ( ( ')' ) )
            // InternalMiniJava.g:3786:1: ( ')' )
            {
            // InternalMiniJava.g:3786:1: ( ')' )
            // InternalMiniJava.g:3787:2: ')'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrintStatementAccess().getRightParenthesisKeyword_7()); 
            }
            match(input,29,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrintStatementAccess().getRightParenthesisKeyword_7()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PrintStatement__Group__7__Impl"


    // $ANTLR start "rule__Return__Group__0"
    // InternalMiniJava.g:3797:1: rule__Return__Group__0 : rule__Return__Group__0__Impl rule__Return__Group__1 ;
    public final void rule__Return__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3801:1: ( rule__Return__Group__0__Impl rule__Return__Group__1 )
            // InternalMiniJava.g:3802:2: rule__Return__Group__0__Impl rule__Return__Group__1
            {
            pushFollow(FOLLOW_25);
            rule__Return__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Return__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Return__Group__0"


    // $ANTLR start "rule__Return__Group__0__Impl"
    // InternalMiniJava.g:3809:1: rule__Return__Group__0__Impl : ( 'return' ) ;
    public final void rule__Return__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3813:1: ( ( 'return' ) )
            // InternalMiniJava.g:3814:1: ( 'return' )
            {
            // InternalMiniJava.g:3814:1: ( 'return' )
            // InternalMiniJava.g:3815:2: 'return'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getReturnAccess().getReturnKeyword_0()); 
            }
            match(input,34,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getReturnAccess().getReturnKeyword_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Return__Group__0__Impl"


    // $ANTLR start "rule__Return__Group__1"
    // InternalMiniJava.g:3824:1: rule__Return__Group__1 : rule__Return__Group__1__Impl ;
    public final void rule__Return__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3828:1: ( rule__Return__Group__1__Impl )
            // InternalMiniJava.g:3829:2: rule__Return__Group__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Return__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Return__Group__1"


    // $ANTLR start "rule__Return__Group__1__Impl"
    // InternalMiniJava.g:3835:1: rule__Return__Group__1__Impl : ( ( rule__Return__ExpressionAssignment_1 ) ) ;
    public final void rule__Return__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3839:1: ( ( ( rule__Return__ExpressionAssignment_1 ) ) )
            // InternalMiniJava.g:3840:1: ( ( rule__Return__ExpressionAssignment_1 ) )
            {
            // InternalMiniJava.g:3840:1: ( ( rule__Return__ExpressionAssignment_1 ) )
            // InternalMiniJava.g:3841:2: ( rule__Return__ExpressionAssignment_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getReturnAccess().getExpressionAssignment_1()); 
            }
            // InternalMiniJava.g:3842:2: ( rule__Return__ExpressionAssignment_1 )
            // InternalMiniJava.g:3842:3: rule__Return__ExpressionAssignment_1
            {
            pushFollow(FOLLOW_2);
            rule__Return__ExpressionAssignment_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getReturnAccess().getExpressionAssignment_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Return__Group__1__Impl"


    // $ANTLR start "rule__IfStatement__Group__0"
    // InternalMiniJava.g:3851:1: rule__IfStatement__Group__0 : rule__IfStatement__Group__0__Impl rule__IfStatement__Group__1 ;
    public final void rule__IfStatement__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3855:1: ( rule__IfStatement__Group__0__Impl rule__IfStatement__Group__1 )
            // InternalMiniJava.g:3856:2: rule__IfStatement__Group__0__Impl rule__IfStatement__Group__1
            {
            pushFollow(FOLLOW_31);
            rule__IfStatement__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__IfStatement__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__IfStatement__Group__0"


    // $ANTLR start "rule__IfStatement__Group__0__Impl"
    // InternalMiniJava.g:3863:1: rule__IfStatement__Group__0__Impl : ( 'if' ) ;
    public final void rule__IfStatement__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3867:1: ( ( 'if' ) )
            // InternalMiniJava.g:3868:1: ( 'if' )
            {
            // InternalMiniJava.g:3868:1: ( 'if' )
            // InternalMiniJava.g:3869:2: 'if'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getIfStatementAccess().getIfKeyword_0()); 
            }
            match(input,35,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getIfStatementAccess().getIfKeyword_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__IfStatement__Group__0__Impl"


    // $ANTLR start "rule__IfStatement__Group__1"
    // InternalMiniJava.g:3878:1: rule__IfStatement__Group__1 : rule__IfStatement__Group__1__Impl rule__IfStatement__Group__2 ;
    public final void rule__IfStatement__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3882:1: ( rule__IfStatement__Group__1__Impl rule__IfStatement__Group__2 )
            // InternalMiniJava.g:3883:2: rule__IfStatement__Group__1__Impl rule__IfStatement__Group__2
            {
            pushFollow(FOLLOW_25);
            rule__IfStatement__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__IfStatement__Group__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__IfStatement__Group__1"


    // $ANTLR start "rule__IfStatement__Group__1__Impl"
    // InternalMiniJava.g:3890:1: rule__IfStatement__Group__1__Impl : ( '(' ) ;
    public final void rule__IfStatement__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3894:1: ( ( '(' ) )
            // InternalMiniJava.g:3895:1: ( '(' )
            {
            // InternalMiniJava.g:3895:1: ( '(' )
            // InternalMiniJava.g:3896:2: '('
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getIfStatementAccess().getLeftParenthesisKeyword_1()); 
            }
            match(input,28,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getIfStatementAccess().getLeftParenthesisKeyword_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__IfStatement__Group__1__Impl"


    // $ANTLR start "rule__IfStatement__Group__2"
    // InternalMiniJava.g:3905:1: rule__IfStatement__Group__2 : rule__IfStatement__Group__2__Impl rule__IfStatement__Group__3 ;
    public final void rule__IfStatement__Group__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3909:1: ( rule__IfStatement__Group__2__Impl rule__IfStatement__Group__3 )
            // InternalMiniJava.g:3910:2: rule__IfStatement__Group__2__Impl rule__IfStatement__Group__3
            {
            pushFollow(FOLLOW_32);
            rule__IfStatement__Group__2__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__IfStatement__Group__3();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__IfStatement__Group__2"


    // $ANTLR start "rule__IfStatement__Group__2__Impl"
    // InternalMiniJava.g:3917:1: rule__IfStatement__Group__2__Impl : ( ( rule__IfStatement__ExpressionAssignment_2 ) ) ;
    public final void rule__IfStatement__Group__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3921:1: ( ( ( rule__IfStatement__ExpressionAssignment_2 ) ) )
            // InternalMiniJava.g:3922:1: ( ( rule__IfStatement__ExpressionAssignment_2 ) )
            {
            // InternalMiniJava.g:3922:1: ( ( rule__IfStatement__ExpressionAssignment_2 ) )
            // InternalMiniJava.g:3923:2: ( rule__IfStatement__ExpressionAssignment_2 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getIfStatementAccess().getExpressionAssignment_2()); 
            }
            // InternalMiniJava.g:3924:2: ( rule__IfStatement__ExpressionAssignment_2 )
            // InternalMiniJava.g:3924:3: rule__IfStatement__ExpressionAssignment_2
            {
            pushFollow(FOLLOW_2);
            rule__IfStatement__ExpressionAssignment_2();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getIfStatementAccess().getExpressionAssignment_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__IfStatement__Group__2__Impl"


    // $ANTLR start "rule__IfStatement__Group__3"
    // InternalMiniJava.g:3932:1: rule__IfStatement__Group__3 : rule__IfStatement__Group__3__Impl rule__IfStatement__Group__4 ;
    public final void rule__IfStatement__Group__3() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3936:1: ( rule__IfStatement__Group__3__Impl rule__IfStatement__Group__4 )
            // InternalMiniJava.g:3937:2: rule__IfStatement__Group__3__Impl rule__IfStatement__Group__4
            {
            pushFollow(FOLLOW_26);
            rule__IfStatement__Group__3__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__IfStatement__Group__4();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__IfStatement__Group__3"


    // $ANTLR start "rule__IfStatement__Group__3__Impl"
    // InternalMiniJava.g:3944:1: rule__IfStatement__Group__3__Impl : ( ')' ) ;
    public final void rule__IfStatement__Group__3__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3948:1: ( ( ')' ) )
            // InternalMiniJava.g:3949:1: ( ')' )
            {
            // InternalMiniJava.g:3949:1: ( ')' )
            // InternalMiniJava.g:3950:2: ')'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getIfStatementAccess().getRightParenthesisKeyword_3()); 
            }
            match(input,29,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getIfStatementAccess().getRightParenthesisKeyword_3()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__IfStatement__Group__3__Impl"


    // $ANTLR start "rule__IfStatement__Group__4"
    // InternalMiniJava.g:3959:1: rule__IfStatement__Group__4 : rule__IfStatement__Group__4__Impl rule__IfStatement__Group__5 ;
    public final void rule__IfStatement__Group__4() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3963:1: ( rule__IfStatement__Group__4__Impl rule__IfStatement__Group__5 )
            // InternalMiniJava.g:3964:2: rule__IfStatement__Group__4__Impl rule__IfStatement__Group__5
            {
            pushFollow(FOLLOW_33);
            rule__IfStatement__Group__4__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__IfStatement__Group__5();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__IfStatement__Group__4"


    // $ANTLR start "rule__IfStatement__Group__4__Impl"
    // InternalMiniJava.g:3971:1: rule__IfStatement__Group__4__Impl : ( ( rule__IfStatement__ThenBlockAssignment_4 ) ) ;
    public final void rule__IfStatement__Group__4__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3975:1: ( ( ( rule__IfStatement__ThenBlockAssignment_4 ) ) )
            // InternalMiniJava.g:3976:1: ( ( rule__IfStatement__ThenBlockAssignment_4 ) )
            {
            // InternalMiniJava.g:3976:1: ( ( rule__IfStatement__ThenBlockAssignment_4 ) )
            // InternalMiniJava.g:3977:2: ( rule__IfStatement__ThenBlockAssignment_4 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getIfStatementAccess().getThenBlockAssignment_4()); 
            }
            // InternalMiniJava.g:3978:2: ( rule__IfStatement__ThenBlockAssignment_4 )
            // InternalMiniJava.g:3978:3: rule__IfStatement__ThenBlockAssignment_4
            {
            pushFollow(FOLLOW_2);
            rule__IfStatement__ThenBlockAssignment_4();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getIfStatementAccess().getThenBlockAssignment_4()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__IfStatement__Group__4__Impl"


    // $ANTLR start "rule__IfStatement__Group__5"
    // InternalMiniJava.g:3986:1: rule__IfStatement__Group__5 : rule__IfStatement__Group__5__Impl ;
    public final void rule__IfStatement__Group__5() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:3990:1: ( rule__IfStatement__Group__5__Impl )
            // InternalMiniJava.g:3991:2: rule__IfStatement__Group__5__Impl
            {
            pushFollow(FOLLOW_2);
            rule__IfStatement__Group__5__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__IfStatement__Group__5"


    // $ANTLR start "rule__IfStatement__Group__5__Impl"
    // InternalMiniJava.g:3997:1: rule__IfStatement__Group__5__Impl : ( ( rule__IfStatement__Group_5__0 )? ) ;
    public final void rule__IfStatement__Group__5__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4001:1: ( ( ( rule__IfStatement__Group_5__0 )? ) )
            // InternalMiniJava.g:4002:1: ( ( rule__IfStatement__Group_5__0 )? )
            {
            // InternalMiniJava.g:4002:1: ( ( rule__IfStatement__Group_5__0 )? )
            // InternalMiniJava.g:4003:2: ( rule__IfStatement__Group_5__0 )?
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getIfStatementAccess().getGroup_5()); 
            }
            // InternalMiniJava.g:4004:2: ( rule__IfStatement__Group_5__0 )?
            int alt42=2;
            int LA42_0 = input.LA(1);

            if ( (LA42_0==36) ) {
                alt42=1;
            }
            switch (alt42) {
                case 1 :
                    // InternalMiniJava.g:4004:3: rule__IfStatement__Group_5__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__IfStatement__Group_5__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getIfStatementAccess().getGroup_5()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__IfStatement__Group__5__Impl"


    // $ANTLR start "rule__IfStatement__Group_5__0"
    // InternalMiniJava.g:4013:1: rule__IfStatement__Group_5__0 : rule__IfStatement__Group_5__0__Impl rule__IfStatement__Group_5__1 ;
    public final void rule__IfStatement__Group_5__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4017:1: ( rule__IfStatement__Group_5__0__Impl rule__IfStatement__Group_5__1 )
            // InternalMiniJava.g:4018:2: rule__IfStatement__Group_5__0__Impl rule__IfStatement__Group_5__1
            {
            pushFollow(FOLLOW_26);
            rule__IfStatement__Group_5__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__IfStatement__Group_5__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__IfStatement__Group_5__0"


    // $ANTLR start "rule__IfStatement__Group_5__0__Impl"
    // InternalMiniJava.g:4025:1: rule__IfStatement__Group_5__0__Impl : ( ( 'else' ) ) ;
    public final void rule__IfStatement__Group_5__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4029:1: ( ( ( 'else' ) ) )
            // InternalMiniJava.g:4030:1: ( ( 'else' ) )
            {
            // InternalMiniJava.g:4030:1: ( ( 'else' ) )
            // InternalMiniJava.g:4031:2: ( 'else' )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getIfStatementAccess().getElseKeyword_5_0()); 
            }
            // InternalMiniJava.g:4032:2: ( 'else' )
            // InternalMiniJava.g:4032:3: 'else'
            {
            match(input,36,FOLLOW_2); if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getIfStatementAccess().getElseKeyword_5_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__IfStatement__Group_5__0__Impl"


    // $ANTLR start "rule__IfStatement__Group_5__1"
    // InternalMiniJava.g:4040:1: rule__IfStatement__Group_5__1 : rule__IfStatement__Group_5__1__Impl ;
    public final void rule__IfStatement__Group_5__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4044:1: ( rule__IfStatement__Group_5__1__Impl )
            // InternalMiniJava.g:4045:2: rule__IfStatement__Group_5__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__IfStatement__Group_5__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__IfStatement__Group_5__1"


    // $ANTLR start "rule__IfStatement__Group_5__1__Impl"
    // InternalMiniJava.g:4051:1: rule__IfStatement__Group_5__1__Impl : ( ( rule__IfStatement__ElseBlockAssignment_5_1 ) ) ;
    public final void rule__IfStatement__Group_5__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4055:1: ( ( ( rule__IfStatement__ElseBlockAssignment_5_1 ) ) )
            // InternalMiniJava.g:4056:1: ( ( rule__IfStatement__ElseBlockAssignment_5_1 ) )
            {
            // InternalMiniJava.g:4056:1: ( ( rule__IfStatement__ElseBlockAssignment_5_1 ) )
            // InternalMiniJava.g:4057:2: ( rule__IfStatement__ElseBlockAssignment_5_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getIfStatementAccess().getElseBlockAssignment_5_1()); 
            }
            // InternalMiniJava.g:4058:2: ( rule__IfStatement__ElseBlockAssignment_5_1 )
            // InternalMiniJava.g:4058:3: rule__IfStatement__ElseBlockAssignment_5_1
            {
            pushFollow(FOLLOW_2);
            rule__IfStatement__ElseBlockAssignment_5_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getIfStatementAccess().getElseBlockAssignment_5_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__IfStatement__Group_5__1__Impl"


    // $ANTLR start "rule__WhileStatement__Group__0"
    // InternalMiniJava.g:4067:1: rule__WhileStatement__Group__0 : rule__WhileStatement__Group__0__Impl rule__WhileStatement__Group__1 ;
    public final void rule__WhileStatement__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4071:1: ( rule__WhileStatement__Group__0__Impl rule__WhileStatement__Group__1 )
            // InternalMiniJava.g:4072:2: rule__WhileStatement__Group__0__Impl rule__WhileStatement__Group__1
            {
            pushFollow(FOLLOW_31);
            rule__WhileStatement__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__WhileStatement__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__WhileStatement__Group__0"


    // $ANTLR start "rule__WhileStatement__Group__0__Impl"
    // InternalMiniJava.g:4079:1: rule__WhileStatement__Group__0__Impl : ( 'while' ) ;
    public final void rule__WhileStatement__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4083:1: ( ( 'while' ) )
            // InternalMiniJava.g:4084:1: ( 'while' )
            {
            // InternalMiniJava.g:4084:1: ( 'while' )
            // InternalMiniJava.g:4085:2: 'while'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getWhileStatementAccess().getWhileKeyword_0()); 
            }
            match(input,37,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getWhileStatementAccess().getWhileKeyword_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__WhileStatement__Group__0__Impl"


    // $ANTLR start "rule__WhileStatement__Group__1"
    // InternalMiniJava.g:4094:1: rule__WhileStatement__Group__1 : rule__WhileStatement__Group__1__Impl rule__WhileStatement__Group__2 ;
    public final void rule__WhileStatement__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4098:1: ( rule__WhileStatement__Group__1__Impl rule__WhileStatement__Group__2 )
            // InternalMiniJava.g:4099:2: rule__WhileStatement__Group__1__Impl rule__WhileStatement__Group__2
            {
            pushFollow(FOLLOW_25);
            rule__WhileStatement__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__WhileStatement__Group__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__WhileStatement__Group__1"


    // $ANTLR start "rule__WhileStatement__Group__1__Impl"
    // InternalMiniJava.g:4106:1: rule__WhileStatement__Group__1__Impl : ( '(' ) ;
    public final void rule__WhileStatement__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4110:1: ( ( '(' ) )
            // InternalMiniJava.g:4111:1: ( '(' )
            {
            // InternalMiniJava.g:4111:1: ( '(' )
            // InternalMiniJava.g:4112:2: '('
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getWhileStatementAccess().getLeftParenthesisKeyword_1()); 
            }
            match(input,28,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getWhileStatementAccess().getLeftParenthesisKeyword_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__WhileStatement__Group__1__Impl"


    // $ANTLR start "rule__WhileStatement__Group__2"
    // InternalMiniJava.g:4121:1: rule__WhileStatement__Group__2 : rule__WhileStatement__Group__2__Impl rule__WhileStatement__Group__3 ;
    public final void rule__WhileStatement__Group__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4125:1: ( rule__WhileStatement__Group__2__Impl rule__WhileStatement__Group__3 )
            // InternalMiniJava.g:4126:2: rule__WhileStatement__Group__2__Impl rule__WhileStatement__Group__3
            {
            pushFollow(FOLLOW_32);
            rule__WhileStatement__Group__2__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__WhileStatement__Group__3();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__WhileStatement__Group__2"


    // $ANTLR start "rule__WhileStatement__Group__2__Impl"
    // InternalMiniJava.g:4133:1: rule__WhileStatement__Group__2__Impl : ( ( rule__WhileStatement__ConditionAssignment_2 ) ) ;
    public final void rule__WhileStatement__Group__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4137:1: ( ( ( rule__WhileStatement__ConditionAssignment_2 ) ) )
            // InternalMiniJava.g:4138:1: ( ( rule__WhileStatement__ConditionAssignment_2 ) )
            {
            // InternalMiniJava.g:4138:1: ( ( rule__WhileStatement__ConditionAssignment_2 ) )
            // InternalMiniJava.g:4139:2: ( rule__WhileStatement__ConditionAssignment_2 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getWhileStatementAccess().getConditionAssignment_2()); 
            }
            // InternalMiniJava.g:4140:2: ( rule__WhileStatement__ConditionAssignment_2 )
            // InternalMiniJava.g:4140:3: rule__WhileStatement__ConditionAssignment_2
            {
            pushFollow(FOLLOW_2);
            rule__WhileStatement__ConditionAssignment_2();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getWhileStatementAccess().getConditionAssignment_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__WhileStatement__Group__2__Impl"


    // $ANTLR start "rule__WhileStatement__Group__3"
    // InternalMiniJava.g:4148:1: rule__WhileStatement__Group__3 : rule__WhileStatement__Group__3__Impl rule__WhileStatement__Group__4 ;
    public final void rule__WhileStatement__Group__3() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4152:1: ( rule__WhileStatement__Group__3__Impl rule__WhileStatement__Group__4 )
            // InternalMiniJava.g:4153:2: rule__WhileStatement__Group__3__Impl rule__WhileStatement__Group__4
            {
            pushFollow(FOLLOW_26);
            rule__WhileStatement__Group__3__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__WhileStatement__Group__4();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__WhileStatement__Group__3"


    // $ANTLR start "rule__WhileStatement__Group__3__Impl"
    // InternalMiniJava.g:4160:1: rule__WhileStatement__Group__3__Impl : ( ')' ) ;
    public final void rule__WhileStatement__Group__3__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4164:1: ( ( ')' ) )
            // InternalMiniJava.g:4165:1: ( ')' )
            {
            // InternalMiniJava.g:4165:1: ( ')' )
            // InternalMiniJava.g:4166:2: ')'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getWhileStatementAccess().getRightParenthesisKeyword_3()); 
            }
            match(input,29,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getWhileStatementAccess().getRightParenthesisKeyword_3()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__WhileStatement__Group__3__Impl"


    // $ANTLR start "rule__WhileStatement__Group__4"
    // InternalMiniJava.g:4175:1: rule__WhileStatement__Group__4 : rule__WhileStatement__Group__4__Impl ;
    public final void rule__WhileStatement__Group__4() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4179:1: ( rule__WhileStatement__Group__4__Impl )
            // InternalMiniJava.g:4180:2: rule__WhileStatement__Group__4__Impl
            {
            pushFollow(FOLLOW_2);
            rule__WhileStatement__Group__4__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__WhileStatement__Group__4"


    // $ANTLR start "rule__WhileStatement__Group__4__Impl"
    // InternalMiniJava.g:4186:1: rule__WhileStatement__Group__4__Impl : ( ( rule__WhileStatement__BlockAssignment_4 ) ) ;
    public final void rule__WhileStatement__Group__4__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4190:1: ( ( ( rule__WhileStatement__BlockAssignment_4 ) ) )
            // InternalMiniJava.g:4191:1: ( ( rule__WhileStatement__BlockAssignment_4 ) )
            {
            // InternalMiniJava.g:4191:1: ( ( rule__WhileStatement__BlockAssignment_4 ) )
            // InternalMiniJava.g:4192:2: ( rule__WhileStatement__BlockAssignment_4 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getWhileStatementAccess().getBlockAssignment_4()); 
            }
            // InternalMiniJava.g:4193:2: ( rule__WhileStatement__BlockAssignment_4 )
            // InternalMiniJava.g:4193:3: rule__WhileStatement__BlockAssignment_4
            {
            pushFollow(FOLLOW_2);
            rule__WhileStatement__BlockAssignment_4();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getWhileStatementAccess().getBlockAssignment_4()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__WhileStatement__Group__4__Impl"


    // $ANTLR start "rule__ForStatement__Group__0"
    // InternalMiniJava.g:4202:1: rule__ForStatement__Group__0 : rule__ForStatement__Group__0__Impl rule__ForStatement__Group__1 ;
    public final void rule__ForStatement__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4206:1: ( rule__ForStatement__Group__0__Impl rule__ForStatement__Group__1 )
            // InternalMiniJava.g:4207:2: rule__ForStatement__Group__0__Impl rule__ForStatement__Group__1
            {
            pushFollow(FOLLOW_31);
            rule__ForStatement__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__ForStatement__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ForStatement__Group__0"


    // $ANTLR start "rule__ForStatement__Group__0__Impl"
    // InternalMiniJava.g:4214:1: rule__ForStatement__Group__0__Impl : ( 'for' ) ;
    public final void rule__ForStatement__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4218:1: ( ( 'for' ) )
            // InternalMiniJava.g:4219:1: ( 'for' )
            {
            // InternalMiniJava.g:4219:1: ( 'for' )
            // InternalMiniJava.g:4220:2: 'for'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getForStatementAccess().getForKeyword_0()); 
            }
            match(input,38,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getForStatementAccess().getForKeyword_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ForStatement__Group__0__Impl"


    // $ANTLR start "rule__ForStatement__Group__1"
    // InternalMiniJava.g:4229:1: rule__ForStatement__Group__1 : rule__ForStatement__Group__1__Impl rule__ForStatement__Group__2 ;
    public final void rule__ForStatement__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4233:1: ( rule__ForStatement__Group__1__Impl rule__ForStatement__Group__2 )
            // InternalMiniJava.g:4234:2: rule__ForStatement__Group__1__Impl rule__ForStatement__Group__2
            {
            pushFollow(FOLLOW_34);
            rule__ForStatement__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__ForStatement__Group__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ForStatement__Group__1"


    // $ANTLR start "rule__ForStatement__Group__1__Impl"
    // InternalMiniJava.g:4241:1: rule__ForStatement__Group__1__Impl : ( '(' ) ;
    public final void rule__ForStatement__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4245:1: ( ( '(' ) )
            // InternalMiniJava.g:4246:1: ( '(' )
            {
            // InternalMiniJava.g:4246:1: ( '(' )
            // InternalMiniJava.g:4247:2: '('
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getForStatementAccess().getLeftParenthesisKeyword_1()); 
            }
            match(input,28,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getForStatementAccess().getLeftParenthesisKeyword_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ForStatement__Group__1__Impl"


    // $ANTLR start "rule__ForStatement__Group__2"
    // InternalMiniJava.g:4256:1: rule__ForStatement__Group__2 : rule__ForStatement__Group__2__Impl rule__ForStatement__Group__3 ;
    public final void rule__ForStatement__Group__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4260:1: ( rule__ForStatement__Group__2__Impl rule__ForStatement__Group__3 )
            // InternalMiniJava.g:4261:2: rule__ForStatement__Group__2__Impl rule__ForStatement__Group__3
            {
            pushFollow(FOLLOW_7);
            rule__ForStatement__Group__2__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__ForStatement__Group__3();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ForStatement__Group__2"


    // $ANTLR start "rule__ForStatement__Group__2__Impl"
    // InternalMiniJava.g:4268:1: rule__ForStatement__Group__2__Impl : ( ( rule__ForStatement__DeclarationAssignment_2 ) ) ;
    public final void rule__ForStatement__Group__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4272:1: ( ( ( rule__ForStatement__DeclarationAssignment_2 ) ) )
            // InternalMiniJava.g:4273:1: ( ( rule__ForStatement__DeclarationAssignment_2 ) )
            {
            // InternalMiniJava.g:4273:1: ( ( rule__ForStatement__DeclarationAssignment_2 ) )
            // InternalMiniJava.g:4274:2: ( rule__ForStatement__DeclarationAssignment_2 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getForStatementAccess().getDeclarationAssignment_2()); 
            }
            // InternalMiniJava.g:4275:2: ( rule__ForStatement__DeclarationAssignment_2 )
            // InternalMiniJava.g:4275:3: rule__ForStatement__DeclarationAssignment_2
            {
            pushFollow(FOLLOW_2);
            rule__ForStatement__DeclarationAssignment_2();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getForStatementAccess().getDeclarationAssignment_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ForStatement__Group__2__Impl"


    // $ANTLR start "rule__ForStatement__Group__3"
    // InternalMiniJava.g:4283:1: rule__ForStatement__Group__3 : rule__ForStatement__Group__3__Impl rule__ForStatement__Group__4 ;
    public final void rule__ForStatement__Group__3() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4287:1: ( rule__ForStatement__Group__3__Impl rule__ForStatement__Group__4 )
            // InternalMiniJava.g:4288:2: rule__ForStatement__Group__3__Impl rule__ForStatement__Group__4
            {
            pushFollow(FOLLOW_25);
            rule__ForStatement__Group__3__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__ForStatement__Group__4();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ForStatement__Group__3"


    // $ANTLR start "rule__ForStatement__Group__3__Impl"
    // InternalMiniJava.g:4295:1: rule__ForStatement__Group__3__Impl : ( ';' ) ;
    public final void rule__ForStatement__Group__3__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4299:1: ( ( ';' ) )
            // InternalMiniJava.g:4300:1: ( ';' )
            {
            // InternalMiniJava.g:4300:1: ( ';' )
            // InternalMiniJava.g:4301:2: ';'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getForStatementAccess().getSemicolonKeyword_3()); 
            }
            match(input,11,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getForStatementAccess().getSemicolonKeyword_3()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ForStatement__Group__3__Impl"


    // $ANTLR start "rule__ForStatement__Group__4"
    // InternalMiniJava.g:4310:1: rule__ForStatement__Group__4 : rule__ForStatement__Group__4__Impl rule__ForStatement__Group__5 ;
    public final void rule__ForStatement__Group__4() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4314:1: ( rule__ForStatement__Group__4__Impl rule__ForStatement__Group__5 )
            // InternalMiniJava.g:4315:2: rule__ForStatement__Group__4__Impl rule__ForStatement__Group__5
            {
            pushFollow(FOLLOW_7);
            rule__ForStatement__Group__4__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__ForStatement__Group__5();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ForStatement__Group__4"


    // $ANTLR start "rule__ForStatement__Group__4__Impl"
    // InternalMiniJava.g:4322:1: rule__ForStatement__Group__4__Impl : ( ( rule__ForStatement__ConditionAssignment_4 ) ) ;
    public final void rule__ForStatement__Group__4__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4326:1: ( ( ( rule__ForStatement__ConditionAssignment_4 ) ) )
            // InternalMiniJava.g:4327:1: ( ( rule__ForStatement__ConditionAssignment_4 ) )
            {
            // InternalMiniJava.g:4327:1: ( ( rule__ForStatement__ConditionAssignment_4 ) )
            // InternalMiniJava.g:4328:2: ( rule__ForStatement__ConditionAssignment_4 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getForStatementAccess().getConditionAssignment_4()); 
            }
            // InternalMiniJava.g:4329:2: ( rule__ForStatement__ConditionAssignment_4 )
            // InternalMiniJava.g:4329:3: rule__ForStatement__ConditionAssignment_4
            {
            pushFollow(FOLLOW_2);
            rule__ForStatement__ConditionAssignment_4();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getForStatementAccess().getConditionAssignment_4()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ForStatement__Group__4__Impl"


    // $ANTLR start "rule__ForStatement__Group__5"
    // InternalMiniJava.g:4337:1: rule__ForStatement__Group__5 : rule__ForStatement__Group__5__Impl rule__ForStatement__Group__6 ;
    public final void rule__ForStatement__Group__5() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4341:1: ( rule__ForStatement__Group__5__Impl rule__ForStatement__Group__6 )
            // InternalMiniJava.g:4342:2: rule__ForStatement__Group__5__Impl rule__ForStatement__Group__6
            {
            pushFollow(FOLLOW_34);
            rule__ForStatement__Group__5__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__ForStatement__Group__6();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ForStatement__Group__5"


    // $ANTLR start "rule__ForStatement__Group__5__Impl"
    // InternalMiniJava.g:4349:1: rule__ForStatement__Group__5__Impl : ( ';' ) ;
    public final void rule__ForStatement__Group__5__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4353:1: ( ( ';' ) )
            // InternalMiniJava.g:4354:1: ( ';' )
            {
            // InternalMiniJava.g:4354:1: ( ';' )
            // InternalMiniJava.g:4355:2: ';'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getForStatementAccess().getSemicolonKeyword_5()); 
            }
            match(input,11,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getForStatementAccess().getSemicolonKeyword_5()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ForStatement__Group__5__Impl"


    // $ANTLR start "rule__ForStatement__Group__6"
    // InternalMiniJava.g:4364:1: rule__ForStatement__Group__6 : rule__ForStatement__Group__6__Impl rule__ForStatement__Group__7 ;
    public final void rule__ForStatement__Group__6() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4368:1: ( rule__ForStatement__Group__6__Impl rule__ForStatement__Group__7 )
            // InternalMiniJava.g:4369:2: rule__ForStatement__Group__6__Impl rule__ForStatement__Group__7
            {
            pushFollow(FOLLOW_32);
            rule__ForStatement__Group__6__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__ForStatement__Group__7();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ForStatement__Group__6"


    // $ANTLR start "rule__ForStatement__Group__6__Impl"
    // InternalMiniJava.g:4376:1: rule__ForStatement__Group__6__Impl : ( ( rule__ForStatement__ProgressionAssignment_6 ) ) ;
    public final void rule__ForStatement__Group__6__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4380:1: ( ( ( rule__ForStatement__ProgressionAssignment_6 ) ) )
            // InternalMiniJava.g:4381:1: ( ( rule__ForStatement__ProgressionAssignment_6 ) )
            {
            // InternalMiniJava.g:4381:1: ( ( rule__ForStatement__ProgressionAssignment_6 ) )
            // InternalMiniJava.g:4382:2: ( rule__ForStatement__ProgressionAssignment_6 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getForStatementAccess().getProgressionAssignment_6()); 
            }
            // InternalMiniJava.g:4383:2: ( rule__ForStatement__ProgressionAssignment_6 )
            // InternalMiniJava.g:4383:3: rule__ForStatement__ProgressionAssignment_6
            {
            pushFollow(FOLLOW_2);
            rule__ForStatement__ProgressionAssignment_6();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getForStatementAccess().getProgressionAssignment_6()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ForStatement__Group__6__Impl"


    // $ANTLR start "rule__ForStatement__Group__7"
    // InternalMiniJava.g:4391:1: rule__ForStatement__Group__7 : rule__ForStatement__Group__7__Impl rule__ForStatement__Group__8 ;
    public final void rule__ForStatement__Group__7() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4395:1: ( rule__ForStatement__Group__7__Impl rule__ForStatement__Group__8 )
            // InternalMiniJava.g:4396:2: rule__ForStatement__Group__7__Impl rule__ForStatement__Group__8
            {
            pushFollow(FOLLOW_26);
            rule__ForStatement__Group__7__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__ForStatement__Group__8();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ForStatement__Group__7"


    // $ANTLR start "rule__ForStatement__Group__7__Impl"
    // InternalMiniJava.g:4403:1: rule__ForStatement__Group__7__Impl : ( ')' ) ;
    public final void rule__ForStatement__Group__7__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4407:1: ( ( ')' ) )
            // InternalMiniJava.g:4408:1: ( ')' )
            {
            // InternalMiniJava.g:4408:1: ( ')' )
            // InternalMiniJava.g:4409:2: ')'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getForStatementAccess().getRightParenthesisKeyword_7()); 
            }
            match(input,29,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getForStatementAccess().getRightParenthesisKeyword_7()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ForStatement__Group__7__Impl"


    // $ANTLR start "rule__ForStatement__Group__8"
    // InternalMiniJava.g:4418:1: rule__ForStatement__Group__8 : rule__ForStatement__Group__8__Impl ;
    public final void rule__ForStatement__Group__8() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4422:1: ( rule__ForStatement__Group__8__Impl )
            // InternalMiniJava.g:4423:2: rule__ForStatement__Group__8__Impl
            {
            pushFollow(FOLLOW_2);
            rule__ForStatement__Group__8__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ForStatement__Group__8"


    // $ANTLR start "rule__ForStatement__Group__8__Impl"
    // InternalMiniJava.g:4429:1: rule__ForStatement__Group__8__Impl : ( ( rule__ForStatement__BlockAssignment_8 ) ) ;
    public final void rule__ForStatement__Group__8__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4433:1: ( ( ( rule__ForStatement__BlockAssignment_8 ) ) )
            // InternalMiniJava.g:4434:1: ( ( rule__ForStatement__BlockAssignment_8 ) )
            {
            // InternalMiniJava.g:4434:1: ( ( rule__ForStatement__BlockAssignment_8 ) )
            // InternalMiniJava.g:4435:2: ( rule__ForStatement__BlockAssignment_8 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getForStatementAccess().getBlockAssignment_8()); 
            }
            // InternalMiniJava.g:4436:2: ( rule__ForStatement__BlockAssignment_8 )
            // InternalMiniJava.g:4436:3: rule__ForStatement__BlockAssignment_8
            {
            pushFollow(FOLLOW_2);
            rule__ForStatement__BlockAssignment_8();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getForStatementAccess().getBlockAssignment_8()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ForStatement__Group__8__Impl"


    // $ANTLR start "rule__TypeRef__Group__0"
    // InternalMiniJava.g:4445:1: rule__TypeRef__Group__0 : rule__TypeRef__Group__0__Impl rule__TypeRef__Group__1 ;
    public final void rule__TypeRef__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4449:1: ( rule__TypeRef__Group__0__Impl rule__TypeRef__Group__1 )
            // InternalMiniJava.g:4450:2: rule__TypeRef__Group__0__Impl rule__TypeRef__Group__1
            {
            pushFollow(FOLLOW_35);
            rule__TypeRef__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__TypeRef__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TypeRef__Group__0"


    // $ANTLR start "rule__TypeRef__Group__0__Impl"
    // InternalMiniJava.g:4457:1: rule__TypeRef__Group__0__Impl : ( ruleSingleTypeRef ) ;
    public final void rule__TypeRef__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4461:1: ( ( ruleSingleTypeRef ) )
            // InternalMiniJava.g:4462:1: ( ruleSingleTypeRef )
            {
            // InternalMiniJava.g:4462:1: ( ruleSingleTypeRef )
            // InternalMiniJava.g:4463:2: ruleSingleTypeRef
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTypeRefAccess().getSingleTypeRefParserRuleCall_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleSingleTypeRef();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTypeRefAccess().getSingleTypeRefParserRuleCall_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TypeRef__Group__0__Impl"


    // $ANTLR start "rule__TypeRef__Group__1"
    // InternalMiniJava.g:4472:1: rule__TypeRef__Group__1 : rule__TypeRef__Group__1__Impl ;
    public final void rule__TypeRef__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4476:1: ( rule__TypeRef__Group__1__Impl )
            // InternalMiniJava.g:4477:2: rule__TypeRef__Group__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__TypeRef__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TypeRef__Group__1"


    // $ANTLR start "rule__TypeRef__Group__1__Impl"
    // InternalMiniJava.g:4483:1: rule__TypeRef__Group__1__Impl : ( ( rule__TypeRef__Group_1__0 )? ) ;
    public final void rule__TypeRef__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4487:1: ( ( ( rule__TypeRef__Group_1__0 )? ) )
            // InternalMiniJava.g:4488:1: ( ( rule__TypeRef__Group_1__0 )? )
            {
            // InternalMiniJava.g:4488:1: ( ( rule__TypeRef__Group_1__0 )? )
            // InternalMiniJava.g:4489:2: ( rule__TypeRef__Group_1__0 )?
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTypeRefAccess().getGroup_1()); 
            }
            // InternalMiniJava.g:4490:2: ( rule__TypeRef__Group_1__0 )?
            int alt43=2;
            int LA43_0 = input.LA(1);

            if ( (LA43_0==39) ) {
                int LA43_1 = input.LA(2);

                if ( (LA43_1==40) ) {
                    alt43=1;
                }
            }
            switch (alt43) {
                case 1 :
                    // InternalMiniJava.g:4490:3: rule__TypeRef__Group_1__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__TypeRef__Group_1__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTypeRefAccess().getGroup_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TypeRef__Group__1__Impl"


    // $ANTLR start "rule__TypeRef__Group_1__0"
    // InternalMiniJava.g:4499:1: rule__TypeRef__Group_1__0 : rule__TypeRef__Group_1__0__Impl rule__TypeRef__Group_1__1 ;
    public final void rule__TypeRef__Group_1__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4503:1: ( rule__TypeRef__Group_1__0__Impl rule__TypeRef__Group_1__1 )
            // InternalMiniJava.g:4504:2: rule__TypeRef__Group_1__0__Impl rule__TypeRef__Group_1__1
            {
            pushFollow(FOLLOW_35);
            rule__TypeRef__Group_1__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__TypeRef__Group_1__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TypeRef__Group_1__0"


    // $ANTLR start "rule__TypeRef__Group_1__0__Impl"
    // InternalMiniJava.g:4511:1: rule__TypeRef__Group_1__0__Impl : ( () ) ;
    public final void rule__TypeRef__Group_1__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4515:1: ( ( () ) )
            // InternalMiniJava.g:4516:1: ( () )
            {
            // InternalMiniJava.g:4516:1: ( () )
            // InternalMiniJava.g:4517:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTypeRefAccess().getArrayTypeRefTypeRefAction_1_0()); 
            }
            // InternalMiniJava.g:4518:2: ()
            // InternalMiniJava.g:4518:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTypeRefAccess().getArrayTypeRefTypeRefAction_1_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TypeRef__Group_1__0__Impl"


    // $ANTLR start "rule__TypeRef__Group_1__1"
    // InternalMiniJava.g:4526:1: rule__TypeRef__Group_1__1 : rule__TypeRef__Group_1__1__Impl rule__TypeRef__Group_1__2 ;
    public final void rule__TypeRef__Group_1__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4530:1: ( rule__TypeRef__Group_1__1__Impl rule__TypeRef__Group_1__2 )
            // InternalMiniJava.g:4531:2: rule__TypeRef__Group_1__1__Impl rule__TypeRef__Group_1__2
            {
            pushFollow(FOLLOW_36);
            rule__TypeRef__Group_1__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__TypeRef__Group_1__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TypeRef__Group_1__1"


    // $ANTLR start "rule__TypeRef__Group_1__1__Impl"
    // InternalMiniJava.g:4538:1: rule__TypeRef__Group_1__1__Impl : ( '[' ) ;
    public final void rule__TypeRef__Group_1__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4542:1: ( ( '[' ) )
            // InternalMiniJava.g:4543:1: ( '[' )
            {
            // InternalMiniJava.g:4543:1: ( '[' )
            // InternalMiniJava.g:4544:2: '['
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTypeRefAccess().getLeftSquareBracketKeyword_1_1()); 
            }
            match(input,39,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTypeRefAccess().getLeftSquareBracketKeyword_1_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TypeRef__Group_1__1__Impl"


    // $ANTLR start "rule__TypeRef__Group_1__2"
    // InternalMiniJava.g:4553:1: rule__TypeRef__Group_1__2 : rule__TypeRef__Group_1__2__Impl ;
    public final void rule__TypeRef__Group_1__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4557:1: ( rule__TypeRef__Group_1__2__Impl )
            // InternalMiniJava.g:4558:2: rule__TypeRef__Group_1__2__Impl
            {
            pushFollow(FOLLOW_2);
            rule__TypeRef__Group_1__2__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TypeRef__Group_1__2"


    // $ANTLR start "rule__TypeRef__Group_1__2__Impl"
    // InternalMiniJava.g:4564:1: rule__TypeRef__Group_1__2__Impl : ( ']' ) ;
    public final void rule__TypeRef__Group_1__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4568:1: ( ( ']' ) )
            // InternalMiniJava.g:4569:1: ( ']' )
            {
            // InternalMiniJava.g:4569:1: ( ']' )
            // InternalMiniJava.g:4570:2: ']'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTypeRefAccess().getRightSquareBracketKeyword_1_2()); 
            }
            match(input,40,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTypeRefAccess().getRightSquareBracketKeyword_1_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TypeRef__Group_1__2__Impl"


    // $ANTLR start "rule__SingleTypeRef__Group_1__0"
    // InternalMiniJava.g:4580:1: rule__SingleTypeRef__Group_1__0 : rule__SingleTypeRef__Group_1__0__Impl rule__SingleTypeRef__Group_1__1 ;
    public final void rule__SingleTypeRef__Group_1__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4584:1: ( rule__SingleTypeRef__Group_1__0__Impl rule__SingleTypeRef__Group_1__1 )
            // InternalMiniJava.g:4585:2: rule__SingleTypeRef__Group_1__0__Impl rule__SingleTypeRef__Group_1__1
            {
            pushFollow(FOLLOW_37);
            rule__SingleTypeRef__Group_1__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__SingleTypeRef__Group_1__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SingleTypeRef__Group_1__0"


    // $ANTLR start "rule__SingleTypeRef__Group_1__0__Impl"
    // InternalMiniJava.g:4592:1: rule__SingleTypeRef__Group_1__0__Impl : ( () ) ;
    public final void rule__SingleTypeRef__Group_1__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4596:1: ( ( () ) )
            // InternalMiniJava.g:4597:1: ( () )
            {
            // InternalMiniJava.g:4597:1: ( () )
            // InternalMiniJava.g:4598:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSingleTypeRefAccess().getIntegerTypeRefAction_1_0()); 
            }
            // InternalMiniJava.g:4599:2: ()
            // InternalMiniJava.g:4599:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getSingleTypeRefAccess().getIntegerTypeRefAction_1_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SingleTypeRef__Group_1__0__Impl"


    // $ANTLR start "rule__SingleTypeRef__Group_1__1"
    // InternalMiniJava.g:4607:1: rule__SingleTypeRef__Group_1__1 : rule__SingleTypeRef__Group_1__1__Impl ;
    public final void rule__SingleTypeRef__Group_1__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4611:1: ( rule__SingleTypeRef__Group_1__1__Impl )
            // InternalMiniJava.g:4612:2: rule__SingleTypeRef__Group_1__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__SingleTypeRef__Group_1__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SingleTypeRef__Group_1__1"


    // $ANTLR start "rule__SingleTypeRef__Group_1__1__Impl"
    // InternalMiniJava.g:4618:1: rule__SingleTypeRef__Group_1__1__Impl : ( 'int' ) ;
    public final void rule__SingleTypeRef__Group_1__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4622:1: ( ( 'int' ) )
            // InternalMiniJava.g:4623:1: ( 'int' )
            {
            // InternalMiniJava.g:4623:1: ( 'int' )
            // InternalMiniJava.g:4624:2: 'int'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSingleTypeRefAccess().getIntKeyword_1_1()); 
            }
            match(input,41,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getSingleTypeRefAccess().getIntKeyword_1_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SingleTypeRef__Group_1__1__Impl"


    // $ANTLR start "rule__SingleTypeRef__Group_2__0"
    // InternalMiniJava.g:4634:1: rule__SingleTypeRef__Group_2__0 : rule__SingleTypeRef__Group_2__0__Impl rule__SingleTypeRef__Group_2__1 ;
    public final void rule__SingleTypeRef__Group_2__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4638:1: ( rule__SingleTypeRef__Group_2__0__Impl rule__SingleTypeRef__Group_2__1 )
            // InternalMiniJava.g:4639:2: rule__SingleTypeRef__Group_2__0__Impl rule__SingleTypeRef__Group_2__1
            {
            pushFollow(FOLLOW_38);
            rule__SingleTypeRef__Group_2__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__SingleTypeRef__Group_2__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SingleTypeRef__Group_2__0"


    // $ANTLR start "rule__SingleTypeRef__Group_2__0__Impl"
    // InternalMiniJava.g:4646:1: rule__SingleTypeRef__Group_2__0__Impl : ( () ) ;
    public final void rule__SingleTypeRef__Group_2__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4650:1: ( ( () ) )
            // InternalMiniJava.g:4651:1: ( () )
            {
            // InternalMiniJava.g:4651:1: ( () )
            // InternalMiniJava.g:4652:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSingleTypeRefAccess().getBooleanTypeRefAction_2_0()); 
            }
            // InternalMiniJava.g:4653:2: ()
            // InternalMiniJava.g:4653:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getSingleTypeRefAccess().getBooleanTypeRefAction_2_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SingleTypeRef__Group_2__0__Impl"


    // $ANTLR start "rule__SingleTypeRef__Group_2__1"
    // InternalMiniJava.g:4661:1: rule__SingleTypeRef__Group_2__1 : rule__SingleTypeRef__Group_2__1__Impl ;
    public final void rule__SingleTypeRef__Group_2__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4665:1: ( rule__SingleTypeRef__Group_2__1__Impl )
            // InternalMiniJava.g:4666:2: rule__SingleTypeRef__Group_2__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__SingleTypeRef__Group_2__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SingleTypeRef__Group_2__1"


    // $ANTLR start "rule__SingleTypeRef__Group_2__1__Impl"
    // InternalMiniJava.g:4672:1: rule__SingleTypeRef__Group_2__1__Impl : ( 'boolean' ) ;
    public final void rule__SingleTypeRef__Group_2__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4676:1: ( ( 'boolean' ) )
            // InternalMiniJava.g:4677:1: ( 'boolean' )
            {
            // InternalMiniJava.g:4677:1: ( 'boolean' )
            // InternalMiniJava.g:4678:2: 'boolean'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSingleTypeRefAccess().getBooleanKeyword_2_1()); 
            }
            match(input,42,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getSingleTypeRefAccess().getBooleanKeyword_2_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SingleTypeRef__Group_2__1__Impl"


    // $ANTLR start "rule__SingleTypeRef__Group_3__0"
    // InternalMiniJava.g:4688:1: rule__SingleTypeRef__Group_3__0 : rule__SingleTypeRef__Group_3__0__Impl rule__SingleTypeRef__Group_3__1 ;
    public final void rule__SingleTypeRef__Group_3__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4692:1: ( rule__SingleTypeRef__Group_3__0__Impl rule__SingleTypeRef__Group_3__1 )
            // InternalMiniJava.g:4693:2: rule__SingleTypeRef__Group_3__0__Impl rule__SingleTypeRef__Group_3__1
            {
            pushFollow(FOLLOW_39);
            rule__SingleTypeRef__Group_3__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__SingleTypeRef__Group_3__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SingleTypeRef__Group_3__0"


    // $ANTLR start "rule__SingleTypeRef__Group_3__0__Impl"
    // InternalMiniJava.g:4700:1: rule__SingleTypeRef__Group_3__0__Impl : ( () ) ;
    public final void rule__SingleTypeRef__Group_3__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4704:1: ( ( () ) )
            // InternalMiniJava.g:4705:1: ( () )
            {
            // InternalMiniJava.g:4705:1: ( () )
            // InternalMiniJava.g:4706:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSingleTypeRefAccess().getStringTypeRefAction_3_0()); 
            }
            // InternalMiniJava.g:4707:2: ()
            // InternalMiniJava.g:4707:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getSingleTypeRefAccess().getStringTypeRefAction_3_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SingleTypeRef__Group_3__0__Impl"


    // $ANTLR start "rule__SingleTypeRef__Group_3__1"
    // InternalMiniJava.g:4715:1: rule__SingleTypeRef__Group_3__1 : rule__SingleTypeRef__Group_3__1__Impl ;
    public final void rule__SingleTypeRef__Group_3__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4719:1: ( rule__SingleTypeRef__Group_3__1__Impl )
            // InternalMiniJava.g:4720:2: rule__SingleTypeRef__Group_3__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__SingleTypeRef__Group_3__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SingleTypeRef__Group_3__1"


    // $ANTLR start "rule__SingleTypeRef__Group_3__1__Impl"
    // InternalMiniJava.g:4726:1: rule__SingleTypeRef__Group_3__1__Impl : ( 'String' ) ;
    public final void rule__SingleTypeRef__Group_3__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4730:1: ( ( 'String' ) )
            // InternalMiniJava.g:4731:1: ( 'String' )
            {
            // InternalMiniJava.g:4731:1: ( 'String' )
            // InternalMiniJava.g:4732:2: 'String'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSingleTypeRefAccess().getStringKeyword_3_1()); 
            }
            match(input,43,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getSingleTypeRefAccess().getStringKeyword_3_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SingleTypeRef__Group_3__1__Impl"


    // $ANTLR start "rule__SingleTypeRef__Group_4__0"
    // InternalMiniJava.g:4742:1: rule__SingleTypeRef__Group_4__0 : rule__SingleTypeRef__Group_4__0__Impl rule__SingleTypeRef__Group_4__1 ;
    public final void rule__SingleTypeRef__Group_4__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4746:1: ( rule__SingleTypeRef__Group_4__0__Impl rule__SingleTypeRef__Group_4__1 )
            // InternalMiniJava.g:4747:2: rule__SingleTypeRef__Group_4__0__Impl rule__SingleTypeRef__Group_4__1
            {
            pushFollow(FOLLOW_23);
            rule__SingleTypeRef__Group_4__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__SingleTypeRef__Group_4__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SingleTypeRef__Group_4__0"


    // $ANTLR start "rule__SingleTypeRef__Group_4__0__Impl"
    // InternalMiniJava.g:4754:1: rule__SingleTypeRef__Group_4__0__Impl : ( () ) ;
    public final void rule__SingleTypeRef__Group_4__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4758:1: ( ( () ) )
            // InternalMiniJava.g:4759:1: ( () )
            {
            // InternalMiniJava.g:4759:1: ( () )
            // InternalMiniJava.g:4760:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSingleTypeRefAccess().getVoidTypeRefAction_4_0()); 
            }
            // InternalMiniJava.g:4761:2: ()
            // InternalMiniJava.g:4761:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getSingleTypeRefAccess().getVoidTypeRefAction_4_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SingleTypeRef__Group_4__0__Impl"


    // $ANTLR start "rule__SingleTypeRef__Group_4__1"
    // InternalMiniJava.g:4769:1: rule__SingleTypeRef__Group_4__1 : rule__SingleTypeRef__Group_4__1__Impl ;
    public final void rule__SingleTypeRef__Group_4__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4773:1: ( rule__SingleTypeRef__Group_4__1__Impl )
            // InternalMiniJava.g:4774:2: rule__SingleTypeRef__Group_4__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__SingleTypeRef__Group_4__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SingleTypeRef__Group_4__1"


    // $ANTLR start "rule__SingleTypeRef__Group_4__1__Impl"
    // InternalMiniJava.g:4780:1: rule__SingleTypeRef__Group_4__1__Impl : ( 'void' ) ;
    public final void rule__SingleTypeRef__Group_4__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4784:1: ( ( 'void' ) )
            // InternalMiniJava.g:4785:1: ( 'void' )
            {
            // InternalMiniJava.g:4785:1: ( 'void' )
            // InternalMiniJava.g:4786:2: 'void'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSingleTypeRefAccess().getVoidKeyword_4_1()); 
            }
            match(input,44,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getSingleTypeRefAccess().getVoidKeyword_4_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SingleTypeRef__Group_4__1__Impl"


    // $ANTLR start "rule__VariableDeclaration__Group__0"
    // InternalMiniJava.g:4796:1: rule__VariableDeclaration__Group__0 : rule__VariableDeclaration__Group__0__Impl rule__VariableDeclaration__Group__1 ;
    public final void rule__VariableDeclaration__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4800:1: ( rule__VariableDeclaration__Group__0__Impl rule__VariableDeclaration__Group__1 )
            // InternalMiniJava.g:4801:2: rule__VariableDeclaration__Group__0__Impl rule__VariableDeclaration__Group__1
            {
            pushFollow(FOLLOW_6);
            rule__VariableDeclaration__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__VariableDeclaration__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__VariableDeclaration__Group__0"


    // $ANTLR start "rule__VariableDeclaration__Group__0__Impl"
    // InternalMiniJava.g:4808:1: rule__VariableDeclaration__Group__0__Impl : ( ( rule__VariableDeclaration__TypeRefAssignment_0 ) ) ;
    public final void rule__VariableDeclaration__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4812:1: ( ( ( rule__VariableDeclaration__TypeRefAssignment_0 ) ) )
            // InternalMiniJava.g:4813:1: ( ( rule__VariableDeclaration__TypeRefAssignment_0 ) )
            {
            // InternalMiniJava.g:4813:1: ( ( rule__VariableDeclaration__TypeRefAssignment_0 ) )
            // InternalMiniJava.g:4814:2: ( rule__VariableDeclaration__TypeRefAssignment_0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getVariableDeclarationAccess().getTypeRefAssignment_0()); 
            }
            // InternalMiniJava.g:4815:2: ( rule__VariableDeclaration__TypeRefAssignment_0 )
            // InternalMiniJava.g:4815:3: rule__VariableDeclaration__TypeRefAssignment_0
            {
            pushFollow(FOLLOW_2);
            rule__VariableDeclaration__TypeRefAssignment_0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getVariableDeclarationAccess().getTypeRefAssignment_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__VariableDeclaration__Group__0__Impl"


    // $ANTLR start "rule__VariableDeclaration__Group__1"
    // InternalMiniJava.g:4823:1: rule__VariableDeclaration__Group__1 : rule__VariableDeclaration__Group__1__Impl ;
    public final void rule__VariableDeclaration__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4827:1: ( rule__VariableDeclaration__Group__1__Impl )
            // InternalMiniJava.g:4828:2: rule__VariableDeclaration__Group__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__VariableDeclaration__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__VariableDeclaration__Group__1"


    // $ANTLR start "rule__VariableDeclaration__Group__1__Impl"
    // InternalMiniJava.g:4834:1: rule__VariableDeclaration__Group__1__Impl : ( ( rule__VariableDeclaration__NameAssignment_1 ) ) ;
    public final void rule__VariableDeclaration__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4838:1: ( ( ( rule__VariableDeclaration__NameAssignment_1 ) ) )
            // InternalMiniJava.g:4839:1: ( ( rule__VariableDeclaration__NameAssignment_1 ) )
            {
            // InternalMiniJava.g:4839:1: ( ( rule__VariableDeclaration__NameAssignment_1 ) )
            // InternalMiniJava.g:4840:2: ( rule__VariableDeclaration__NameAssignment_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getVariableDeclarationAccess().getNameAssignment_1()); 
            }
            // InternalMiniJava.g:4841:2: ( rule__VariableDeclaration__NameAssignment_1 )
            // InternalMiniJava.g:4841:3: rule__VariableDeclaration__NameAssignment_1
            {
            pushFollow(FOLLOW_2);
            rule__VariableDeclaration__NameAssignment_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getVariableDeclarationAccess().getNameAssignment_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__VariableDeclaration__Group__1__Impl"


    // $ANTLR start "rule__Assignment__Group__0"
    // InternalMiniJava.g:4850:1: rule__Assignment__Group__0 : rule__Assignment__Group__0__Impl rule__Assignment__Group__1 ;
    public final void rule__Assignment__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4854:1: ( rule__Assignment__Group__0__Impl rule__Assignment__Group__1 )
            // InternalMiniJava.g:4855:2: rule__Assignment__Group__0__Impl rule__Assignment__Group__1
            {
            pushFollow(FOLLOW_40);
            rule__Assignment__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Assignment__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Assignment__Group__0"


    // $ANTLR start "rule__Assignment__Group__0__Impl"
    // InternalMiniJava.g:4862:1: rule__Assignment__Group__0__Impl : ( ( rule__Assignment__AssigneeAssignment_0 ) ) ;
    public final void rule__Assignment__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4866:1: ( ( ( rule__Assignment__AssigneeAssignment_0 ) ) )
            // InternalMiniJava.g:4867:1: ( ( rule__Assignment__AssigneeAssignment_0 ) )
            {
            // InternalMiniJava.g:4867:1: ( ( rule__Assignment__AssigneeAssignment_0 ) )
            // InternalMiniJava.g:4868:2: ( rule__Assignment__AssigneeAssignment_0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getAssignmentAccess().getAssigneeAssignment_0()); 
            }
            // InternalMiniJava.g:4869:2: ( rule__Assignment__AssigneeAssignment_0 )
            // InternalMiniJava.g:4869:3: rule__Assignment__AssigneeAssignment_0
            {
            pushFollow(FOLLOW_2);
            rule__Assignment__AssigneeAssignment_0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getAssignmentAccess().getAssigneeAssignment_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Assignment__Group__0__Impl"


    // $ANTLR start "rule__Assignment__Group__1"
    // InternalMiniJava.g:4877:1: rule__Assignment__Group__1 : rule__Assignment__Group__1__Impl rule__Assignment__Group__2 ;
    public final void rule__Assignment__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4881:1: ( rule__Assignment__Group__1__Impl rule__Assignment__Group__2 )
            // InternalMiniJava.g:4882:2: rule__Assignment__Group__1__Impl rule__Assignment__Group__2
            {
            pushFollow(FOLLOW_25);
            rule__Assignment__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Assignment__Group__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Assignment__Group__1"


    // $ANTLR start "rule__Assignment__Group__1__Impl"
    // InternalMiniJava.g:4889:1: rule__Assignment__Group__1__Impl : ( '=' ) ;
    public final void rule__Assignment__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4893:1: ( ( '=' ) )
            // InternalMiniJava.g:4894:1: ( '=' )
            {
            // InternalMiniJava.g:4894:1: ( '=' )
            // InternalMiniJava.g:4895:2: '='
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getAssignmentAccess().getEqualsSignKeyword_1()); 
            }
            match(input,30,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getAssignmentAccess().getEqualsSignKeyword_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Assignment__Group__1__Impl"


    // $ANTLR start "rule__Assignment__Group__2"
    // InternalMiniJava.g:4904:1: rule__Assignment__Group__2 : rule__Assignment__Group__2__Impl ;
    public final void rule__Assignment__Group__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4908:1: ( rule__Assignment__Group__2__Impl )
            // InternalMiniJava.g:4909:2: rule__Assignment__Group__2__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Assignment__Group__2__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Assignment__Group__2"


    // $ANTLR start "rule__Assignment__Group__2__Impl"
    // InternalMiniJava.g:4915:1: rule__Assignment__Group__2__Impl : ( ( rule__Assignment__ValueAssignment_2 ) ) ;
    public final void rule__Assignment__Group__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4919:1: ( ( ( rule__Assignment__ValueAssignment_2 ) ) )
            // InternalMiniJava.g:4920:1: ( ( rule__Assignment__ValueAssignment_2 ) )
            {
            // InternalMiniJava.g:4920:1: ( ( rule__Assignment__ValueAssignment_2 ) )
            // InternalMiniJava.g:4921:2: ( rule__Assignment__ValueAssignment_2 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getAssignmentAccess().getValueAssignment_2()); 
            }
            // InternalMiniJava.g:4922:2: ( rule__Assignment__ValueAssignment_2 )
            // InternalMiniJava.g:4922:3: rule__Assignment__ValueAssignment_2
            {
            pushFollow(FOLLOW_2);
            rule__Assignment__ValueAssignment_2();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getAssignmentAccess().getValueAssignment_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Assignment__Group__2__Impl"


    // $ANTLR start "rule__Or__Group__0"
    // InternalMiniJava.g:4931:1: rule__Or__Group__0 : rule__Or__Group__0__Impl rule__Or__Group__1 ;
    public final void rule__Or__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4935:1: ( rule__Or__Group__0__Impl rule__Or__Group__1 )
            // InternalMiniJava.g:4936:2: rule__Or__Group__0__Impl rule__Or__Group__1
            {
            pushFollow(FOLLOW_41);
            rule__Or__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Or__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Or__Group__0"


    // $ANTLR start "rule__Or__Group__0__Impl"
    // InternalMiniJava.g:4943:1: rule__Or__Group__0__Impl : ( ruleAnd ) ;
    public final void rule__Or__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4947:1: ( ( ruleAnd ) )
            // InternalMiniJava.g:4948:1: ( ruleAnd )
            {
            // InternalMiniJava.g:4948:1: ( ruleAnd )
            // InternalMiniJava.g:4949:2: ruleAnd
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getOrAccess().getAndParserRuleCall_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleAnd();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getOrAccess().getAndParserRuleCall_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Or__Group__0__Impl"


    // $ANTLR start "rule__Or__Group__1"
    // InternalMiniJava.g:4958:1: rule__Or__Group__1 : rule__Or__Group__1__Impl ;
    public final void rule__Or__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4962:1: ( rule__Or__Group__1__Impl )
            // InternalMiniJava.g:4963:2: rule__Or__Group__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Or__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Or__Group__1"


    // $ANTLR start "rule__Or__Group__1__Impl"
    // InternalMiniJava.g:4969:1: rule__Or__Group__1__Impl : ( ( rule__Or__Group_1__0 )* ) ;
    public final void rule__Or__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4973:1: ( ( ( rule__Or__Group_1__0 )* ) )
            // InternalMiniJava.g:4974:1: ( ( rule__Or__Group_1__0 )* )
            {
            // InternalMiniJava.g:4974:1: ( ( rule__Or__Group_1__0 )* )
            // InternalMiniJava.g:4975:2: ( rule__Or__Group_1__0 )*
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getOrAccess().getGroup_1()); 
            }
            // InternalMiniJava.g:4976:2: ( rule__Or__Group_1__0 )*
            loop44:
            do {
                int alt44=2;
                int LA44_0 = input.LA(1);

                if ( (LA44_0==45) ) {
                    alt44=1;
                }


                switch (alt44) {
            	case 1 :
            	    // InternalMiniJava.g:4976:3: rule__Or__Group_1__0
            	    {
            	    pushFollow(FOLLOW_42);
            	    rule__Or__Group_1__0();

            	    state._fsp--;
            	    if (state.failed) return ;

            	    }
            	    break;

            	default :
            	    break loop44;
                }
            } while (true);

            if ( state.backtracking==0 ) {
               after(grammarAccess.getOrAccess().getGroup_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Or__Group__1__Impl"


    // $ANTLR start "rule__Or__Group_1__0"
    // InternalMiniJava.g:4985:1: rule__Or__Group_1__0 : rule__Or__Group_1__0__Impl rule__Or__Group_1__1 ;
    public final void rule__Or__Group_1__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:4989:1: ( rule__Or__Group_1__0__Impl rule__Or__Group_1__1 )
            // InternalMiniJava.g:4990:2: rule__Or__Group_1__0__Impl rule__Or__Group_1__1
            {
            pushFollow(FOLLOW_41);
            rule__Or__Group_1__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Or__Group_1__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Or__Group_1__0"


    // $ANTLR start "rule__Or__Group_1__0__Impl"
    // InternalMiniJava.g:4997:1: rule__Or__Group_1__0__Impl : ( () ) ;
    public final void rule__Or__Group_1__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5001:1: ( ( () ) )
            // InternalMiniJava.g:5002:1: ( () )
            {
            // InternalMiniJava.g:5002:1: ( () )
            // InternalMiniJava.g:5003:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getOrAccess().getOrLeftAction_1_0()); 
            }
            // InternalMiniJava.g:5004:2: ()
            // InternalMiniJava.g:5004:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getOrAccess().getOrLeftAction_1_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Or__Group_1__0__Impl"


    // $ANTLR start "rule__Or__Group_1__1"
    // InternalMiniJava.g:5012:1: rule__Or__Group_1__1 : rule__Or__Group_1__1__Impl rule__Or__Group_1__2 ;
    public final void rule__Or__Group_1__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5016:1: ( rule__Or__Group_1__1__Impl rule__Or__Group_1__2 )
            // InternalMiniJava.g:5017:2: rule__Or__Group_1__1__Impl rule__Or__Group_1__2
            {
            pushFollow(FOLLOW_25);
            rule__Or__Group_1__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Or__Group_1__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Or__Group_1__1"


    // $ANTLR start "rule__Or__Group_1__1__Impl"
    // InternalMiniJava.g:5024:1: rule__Or__Group_1__1__Impl : ( '||' ) ;
    public final void rule__Or__Group_1__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5028:1: ( ( '||' ) )
            // InternalMiniJava.g:5029:1: ( '||' )
            {
            // InternalMiniJava.g:5029:1: ( '||' )
            // InternalMiniJava.g:5030:2: '||'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getOrAccess().getVerticalLineVerticalLineKeyword_1_1()); 
            }
            match(input,45,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getOrAccess().getVerticalLineVerticalLineKeyword_1_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Or__Group_1__1__Impl"


    // $ANTLR start "rule__Or__Group_1__2"
    // InternalMiniJava.g:5039:1: rule__Or__Group_1__2 : rule__Or__Group_1__2__Impl ;
    public final void rule__Or__Group_1__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5043:1: ( rule__Or__Group_1__2__Impl )
            // InternalMiniJava.g:5044:2: rule__Or__Group_1__2__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Or__Group_1__2__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Or__Group_1__2"


    // $ANTLR start "rule__Or__Group_1__2__Impl"
    // InternalMiniJava.g:5050:1: rule__Or__Group_1__2__Impl : ( ( rule__Or__RightAssignment_1_2 ) ) ;
    public final void rule__Or__Group_1__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5054:1: ( ( ( rule__Or__RightAssignment_1_2 ) ) )
            // InternalMiniJava.g:5055:1: ( ( rule__Or__RightAssignment_1_2 ) )
            {
            // InternalMiniJava.g:5055:1: ( ( rule__Or__RightAssignment_1_2 ) )
            // InternalMiniJava.g:5056:2: ( rule__Or__RightAssignment_1_2 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getOrAccess().getRightAssignment_1_2()); 
            }
            // InternalMiniJava.g:5057:2: ( rule__Or__RightAssignment_1_2 )
            // InternalMiniJava.g:5057:3: rule__Or__RightAssignment_1_2
            {
            pushFollow(FOLLOW_2);
            rule__Or__RightAssignment_1_2();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getOrAccess().getRightAssignment_1_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Or__Group_1__2__Impl"


    // $ANTLR start "rule__And__Group__0"
    // InternalMiniJava.g:5066:1: rule__And__Group__0 : rule__And__Group__0__Impl rule__And__Group__1 ;
    public final void rule__And__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5070:1: ( rule__And__Group__0__Impl rule__And__Group__1 )
            // InternalMiniJava.g:5071:2: rule__And__Group__0__Impl rule__And__Group__1
            {
            pushFollow(FOLLOW_43);
            rule__And__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__And__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__And__Group__0"


    // $ANTLR start "rule__And__Group__0__Impl"
    // InternalMiniJava.g:5078:1: rule__And__Group__0__Impl : ( ruleEquality ) ;
    public final void rule__And__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5082:1: ( ( ruleEquality ) )
            // InternalMiniJava.g:5083:1: ( ruleEquality )
            {
            // InternalMiniJava.g:5083:1: ( ruleEquality )
            // InternalMiniJava.g:5084:2: ruleEquality
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getAndAccess().getEqualityParserRuleCall_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleEquality();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getAndAccess().getEqualityParserRuleCall_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__And__Group__0__Impl"


    // $ANTLR start "rule__And__Group__1"
    // InternalMiniJava.g:5093:1: rule__And__Group__1 : rule__And__Group__1__Impl ;
    public final void rule__And__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5097:1: ( rule__And__Group__1__Impl )
            // InternalMiniJava.g:5098:2: rule__And__Group__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__And__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__And__Group__1"


    // $ANTLR start "rule__And__Group__1__Impl"
    // InternalMiniJava.g:5104:1: rule__And__Group__1__Impl : ( ( rule__And__Group_1__0 )* ) ;
    public final void rule__And__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5108:1: ( ( ( rule__And__Group_1__0 )* ) )
            // InternalMiniJava.g:5109:1: ( ( rule__And__Group_1__0 )* )
            {
            // InternalMiniJava.g:5109:1: ( ( rule__And__Group_1__0 )* )
            // InternalMiniJava.g:5110:2: ( rule__And__Group_1__0 )*
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getAndAccess().getGroup_1()); 
            }
            // InternalMiniJava.g:5111:2: ( rule__And__Group_1__0 )*
            loop45:
            do {
                int alt45=2;
                int LA45_0 = input.LA(1);

                if ( (LA45_0==46) ) {
                    alt45=1;
                }


                switch (alt45) {
            	case 1 :
            	    // InternalMiniJava.g:5111:3: rule__And__Group_1__0
            	    {
            	    pushFollow(FOLLOW_44);
            	    rule__And__Group_1__0();

            	    state._fsp--;
            	    if (state.failed) return ;

            	    }
            	    break;

            	default :
            	    break loop45;
                }
            } while (true);

            if ( state.backtracking==0 ) {
               after(grammarAccess.getAndAccess().getGroup_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__And__Group__1__Impl"


    // $ANTLR start "rule__And__Group_1__0"
    // InternalMiniJava.g:5120:1: rule__And__Group_1__0 : rule__And__Group_1__0__Impl rule__And__Group_1__1 ;
    public final void rule__And__Group_1__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5124:1: ( rule__And__Group_1__0__Impl rule__And__Group_1__1 )
            // InternalMiniJava.g:5125:2: rule__And__Group_1__0__Impl rule__And__Group_1__1
            {
            pushFollow(FOLLOW_43);
            rule__And__Group_1__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__And__Group_1__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__And__Group_1__0"


    // $ANTLR start "rule__And__Group_1__0__Impl"
    // InternalMiniJava.g:5132:1: rule__And__Group_1__0__Impl : ( () ) ;
    public final void rule__And__Group_1__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5136:1: ( ( () ) )
            // InternalMiniJava.g:5137:1: ( () )
            {
            // InternalMiniJava.g:5137:1: ( () )
            // InternalMiniJava.g:5138:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getAndAccess().getAndLeftAction_1_0()); 
            }
            // InternalMiniJava.g:5139:2: ()
            // InternalMiniJava.g:5139:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getAndAccess().getAndLeftAction_1_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__And__Group_1__0__Impl"


    // $ANTLR start "rule__And__Group_1__1"
    // InternalMiniJava.g:5147:1: rule__And__Group_1__1 : rule__And__Group_1__1__Impl rule__And__Group_1__2 ;
    public final void rule__And__Group_1__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5151:1: ( rule__And__Group_1__1__Impl rule__And__Group_1__2 )
            // InternalMiniJava.g:5152:2: rule__And__Group_1__1__Impl rule__And__Group_1__2
            {
            pushFollow(FOLLOW_25);
            rule__And__Group_1__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__And__Group_1__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__And__Group_1__1"


    // $ANTLR start "rule__And__Group_1__1__Impl"
    // InternalMiniJava.g:5159:1: rule__And__Group_1__1__Impl : ( '&&' ) ;
    public final void rule__And__Group_1__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5163:1: ( ( '&&' ) )
            // InternalMiniJava.g:5164:1: ( '&&' )
            {
            // InternalMiniJava.g:5164:1: ( '&&' )
            // InternalMiniJava.g:5165:2: '&&'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getAndAccess().getAmpersandAmpersandKeyword_1_1()); 
            }
            match(input,46,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getAndAccess().getAmpersandAmpersandKeyword_1_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__And__Group_1__1__Impl"


    // $ANTLR start "rule__And__Group_1__2"
    // InternalMiniJava.g:5174:1: rule__And__Group_1__2 : rule__And__Group_1__2__Impl ;
    public final void rule__And__Group_1__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5178:1: ( rule__And__Group_1__2__Impl )
            // InternalMiniJava.g:5179:2: rule__And__Group_1__2__Impl
            {
            pushFollow(FOLLOW_2);
            rule__And__Group_1__2__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__And__Group_1__2"


    // $ANTLR start "rule__And__Group_1__2__Impl"
    // InternalMiniJava.g:5185:1: rule__And__Group_1__2__Impl : ( ( rule__And__RightAssignment_1_2 ) ) ;
    public final void rule__And__Group_1__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5189:1: ( ( ( rule__And__RightAssignment_1_2 ) ) )
            // InternalMiniJava.g:5190:1: ( ( rule__And__RightAssignment_1_2 ) )
            {
            // InternalMiniJava.g:5190:1: ( ( rule__And__RightAssignment_1_2 ) )
            // InternalMiniJava.g:5191:2: ( rule__And__RightAssignment_1_2 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getAndAccess().getRightAssignment_1_2()); 
            }
            // InternalMiniJava.g:5192:2: ( rule__And__RightAssignment_1_2 )
            // InternalMiniJava.g:5192:3: rule__And__RightAssignment_1_2
            {
            pushFollow(FOLLOW_2);
            rule__And__RightAssignment_1_2();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getAndAccess().getRightAssignment_1_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__And__Group_1__2__Impl"


    // $ANTLR start "rule__Equality__Group__0"
    // InternalMiniJava.g:5201:1: rule__Equality__Group__0 : rule__Equality__Group__0__Impl rule__Equality__Group__1 ;
    public final void rule__Equality__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5205:1: ( rule__Equality__Group__0__Impl rule__Equality__Group__1 )
            // InternalMiniJava.g:5206:2: rule__Equality__Group__0__Impl rule__Equality__Group__1
            {
            pushFollow(FOLLOW_45);
            rule__Equality__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Equality__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Equality__Group__0"


    // $ANTLR start "rule__Equality__Group__0__Impl"
    // InternalMiniJava.g:5213:1: rule__Equality__Group__0__Impl : ( ruleComparison ) ;
    public final void rule__Equality__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5217:1: ( ( ruleComparison ) )
            // InternalMiniJava.g:5218:1: ( ruleComparison )
            {
            // InternalMiniJava.g:5218:1: ( ruleComparison )
            // InternalMiniJava.g:5219:2: ruleComparison
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getEqualityAccess().getComparisonParserRuleCall_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleComparison();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getEqualityAccess().getComparisonParserRuleCall_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Equality__Group__0__Impl"


    // $ANTLR start "rule__Equality__Group__1"
    // InternalMiniJava.g:5228:1: rule__Equality__Group__1 : rule__Equality__Group__1__Impl ;
    public final void rule__Equality__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5232:1: ( rule__Equality__Group__1__Impl )
            // InternalMiniJava.g:5233:2: rule__Equality__Group__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Equality__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Equality__Group__1"


    // $ANTLR start "rule__Equality__Group__1__Impl"
    // InternalMiniJava.g:5239:1: rule__Equality__Group__1__Impl : ( ( rule__Equality__Group_1__0 )* ) ;
    public final void rule__Equality__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5243:1: ( ( ( rule__Equality__Group_1__0 )* ) )
            // InternalMiniJava.g:5244:1: ( ( rule__Equality__Group_1__0 )* )
            {
            // InternalMiniJava.g:5244:1: ( ( rule__Equality__Group_1__0 )* )
            // InternalMiniJava.g:5245:2: ( rule__Equality__Group_1__0 )*
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getEqualityAccess().getGroup_1()); 
            }
            // InternalMiniJava.g:5246:2: ( rule__Equality__Group_1__0 )*
            loop46:
            do {
                int alt46=2;
                int LA46_0 = input.LA(1);

                if ( ((LA46_0>=47 && LA46_0<=48)) ) {
                    alt46=1;
                }


                switch (alt46) {
            	case 1 :
            	    // InternalMiniJava.g:5246:3: rule__Equality__Group_1__0
            	    {
            	    pushFollow(FOLLOW_46);
            	    rule__Equality__Group_1__0();

            	    state._fsp--;
            	    if (state.failed) return ;

            	    }
            	    break;

            	default :
            	    break loop46;
                }
            } while (true);

            if ( state.backtracking==0 ) {
               after(grammarAccess.getEqualityAccess().getGroup_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Equality__Group__1__Impl"


    // $ANTLR start "rule__Equality__Group_1__0"
    // InternalMiniJava.g:5255:1: rule__Equality__Group_1__0 : rule__Equality__Group_1__0__Impl rule__Equality__Group_1__1 ;
    public final void rule__Equality__Group_1__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5259:1: ( rule__Equality__Group_1__0__Impl rule__Equality__Group_1__1 )
            // InternalMiniJava.g:5260:2: rule__Equality__Group_1__0__Impl rule__Equality__Group_1__1
            {
            pushFollow(FOLLOW_25);
            rule__Equality__Group_1__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Equality__Group_1__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Equality__Group_1__0"


    // $ANTLR start "rule__Equality__Group_1__0__Impl"
    // InternalMiniJava.g:5267:1: rule__Equality__Group_1__0__Impl : ( ( rule__Equality__Alternatives_1_0 ) ) ;
    public final void rule__Equality__Group_1__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5271:1: ( ( ( rule__Equality__Alternatives_1_0 ) ) )
            // InternalMiniJava.g:5272:1: ( ( rule__Equality__Alternatives_1_0 ) )
            {
            // InternalMiniJava.g:5272:1: ( ( rule__Equality__Alternatives_1_0 ) )
            // InternalMiniJava.g:5273:2: ( rule__Equality__Alternatives_1_0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getEqualityAccess().getAlternatives_1_0()); 
            }
            // InternalMiniJava.g:5274:2: ( rule__Equality__Alternatives_1_0 )
            // InternalMiniJava.g:5274:3: rule__Equality__Alternatives_1_0
            {
            pushFollow(FOLLOW_2);
            rule__Equality__Alternatives_1_0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getEqualityAccess().getAlternatives_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Equality__Group_1__0__Impl"


    // $ANTLR start "rule__Equality__Group_1__1"
    // InternalMiniJava.g:5282:1: rule__Equality__Group_1__1 : rule__Equality__Group_1__1__Impl ;
    public final void rule__Equality__Group_1__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5286:1: ( rule__Equality__Group_1__1__Impl )
            // InternalMiniJava.g:5287:2: rule__Equality__Group_1__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Equality__Group_1__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Equality__Group_1__1"


    // $ANTLR start "rule__Equality__Group_1__1__Impl"
    // InternalMiniJava.g:5293:1: rule__Equality__Group_1__1__Impl : ( ( rule__Equality__RightAssignment_1_1 ) ) ;
    public final void rule__Equality__Group_1__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5297:1: ( ( ( rule__Equality__RightAssignment_1_1 ) ) )
            // InternalMiniJava.g:5298:1: ( ( rule__Equality__RightAssignment_1_1 ) )
            {
            // InternalMiniJava.g:5298:1: ( ( rule__Equality__RightAssignment_1_1 ) )
            // InternalMiniJava.g:5299:2: ( rule__Equality__RightAssignment_1_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getEqualityAccess().getRightAssignment_1_1()); 
            }
            // InternalMiniJava.g:5300:2: ( rule__Equality__RightAssignment_1_1 )
            // InternalMiniJava.g:5300:3: rule__Equality__RightAssignment_1_1
            {
            pushFollow(FOLLOW_2);
            rule__Equality__RightAssignment_1_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getEqualityAccess().getRightAssignment_1_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Equality__Group_1__1__Impl"


    // $ANTLR start "rule__Equality__Group_1_0_0__0"
    // InternalMiniJava.g:5309:1: rule__Equality__Group_1_0_0__0 : rule__Equality__Group_1_0_0__0__Impl rule__Equality__Group_1_0_0__1 ;
    public final void rule__Equality__Group_1_0_0__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5313:1: ( rule__Equality__Group_1_0_0__0__Impl rule__Equality__Group_1_0_0__1 )
            // InternalMiniJava.g:5314:2: rule__Equality__Group_1_0_0__0__Impl rule__Equality__Group_1_0_0__1
            {
            pushFollow(FOLLOW_47);
            rule__Equality__Group_1_0_0__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Equality__Group_1_0_0__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Equality__Group_1_0_0__0"


    // $ANTLR start "rule__Equality__Group_1_0_0__0__Impl"
    // InternalMiniJava.g:5321:1: rule__Equality__Group_1_0_0__0__Impl : ( () ) ;
    public final void rule__Equality__Group_1_0_0__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5325:1: ( ( () ) )
            // InternalMiniJava.g:5326:1: ( () )
            {
            // InternalMiniJava.g:5326:1: ( () )
            // InternalMiniJava.g:5327:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getEqualityAccess().getEqualityLeftAction_1_0_0_0()); 
            }
            // InternalMiniJava.g:5328:2: ()
            // InternalMiniJava.g:5328:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getEqualityAccess().getEqualityLeftAction_1_0_0_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Equality__Group_1_0_0__0__Impl"


    // $ANTLR start "rule__Equality__Group_1_0_0__1"
    // InternalMiniJava.g:5336:1: rule__Equality__Group_1_0_0__1 : rule__Equality__Group_1_0_0__1__Impl ;
    public final void rule__Equality__Group_1_0_0__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5340:1: ( rule__Equality__Group_1_0_0__1__Impl )
            // InternalMiniJava.g:5341:2: rule__Equality__Group_1_0_0__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Equality__Group_1_0_0__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Equality__Group_1_0_0__1"


    // $ANTLR start "rule__Equality__Group_1_0_0__1__Impl"
    // InternalMiniJava.g:5347:1: rule__Equality__Group_1_0_0__1__Impl : ( '==' ) ;
    public final void rule__Equality__Group_1_0_0__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5351:1: ( ( '==' ) )
            // InternalMiniJava.g:5352:1: ( '==' )
            {
            // InternalMiniJava.g:5352:1: ( '==' )
            // InternalMiniJava.g:5353:2: '=='
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getEqualityAccess().getEqualsSignEqualsSignKeyword_1_0_0_1()); 
            }
            match(input,47,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getEqualityAccess().getEqualsSignEqualsSignKeyword_1_0_0_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Equality__Group_1_0_0__1__Impl"


    // $ANTLR start "rule__Equality__Group_1_0_1__0"
    // InternalMiniJava.g:5363:1: rule__Equality__Group_1_0_1__0 : rule__Equality__Group_1_0_1__0__Impl rule__Equality__Group_1_0_1__1 ;
    public final void rule__Equality__Group_1_0_1__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5367:1: ( rule__Equality__Group_1_0_1__0__Impl rule__Equality__Group_1_0_1__1 )
            // InternalMiniJava.g:5368:2: rule__Equality__Group_1_0_1__0__Impl rule__Equality__Group_1_0_1__1
            {
            pushFollow(FOLLOW_45);
            rule__Equality__Group_1_0_1__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Equality__Group_1_0_1__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Equality__Group_1_0_1__0"


    // $ANTLR start "rule__Equality__Group_1_0_1__0__Impl"
    // InternalMiniJava.g:5375:1: rule__Equality__Group_1_0_1__0__Impl : ( () ) ;
    public final void rule__Equality__Group_1_0_1__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5379:1: ( ( () ) )
            // InternalMiniJava.g:5380:1: ( () )
            {
            // InternalMiniJava.g:5380:1: ( () )
            // InternalMiniJava.g:5381:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getEqualityAccess().getInequalityLeftAction_1_0_1_0()); 
            }
            // InternalMiniJava.g:5382:2: ()
            // InternalMiniJava.g:5382:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getEqualityAccess().getInequalityLeftAction_1_0_1_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Equality__Group_1_0_1__0__Impl"


    // $ANTLR start "rule__Equality__Group_1_0_1__1"
    // InternalMiniJava.g:5390:1: rule__Equality__Group_1_0_1__1 : rule__Equality__Group_1_0_1__1__Impl ;
    public final void rule__Equality__Group_1_0_1__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5394:1: ( rule__Equality__Group_1_0_1__1__Impl )
            // InternalMiniJava.g:5395:2: rule__Equality__Group_1_0_1__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Equality__Group_1_0_1__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Equality__Group_1_0_1__1"


    // $ANTLR start "rule__Equality__Group_1_0_1__1__Impl"
    // InternalMiniJava.g:5401:1: rule__Equality__Group_1_0_1__1__Impl : ( '!=' ) ;
    public final void rule__Equality__Group_1_0_1__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5405:1: ( ( '!=' ) )
            // InternalMiniJava.g:5406:1: ( '!=' )
            {
            // InternalMiniJava.g:5406:1: ( '!=' )
            // InternalMiniJava.g:5407:2: '!='
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getEqualityAccess().getExclamationMarkEqualsSignKeyword_1_0_1_1()); 
            }
            match(input,48,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getEqualityAccess().getExclamationMarkEqualsSignKeyword_1_0_1_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Equality__Group_1_0_1__1__Impl"


    // $ANTLR start "rule__Comparison__Group__0"
    // InternalMiniJava.g:5417:1: rule__Comparison__Group__0 : rule__Comparison__Group__0__Impl rule__Comparison__Group__1 ;
    public final void rule__Comparison__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5421:1: ( rule__Comparison__Group__0__Impl rule__Comparison__Group__1 )
            // InternalMiniJava.g:5422:2: rule__Comparison__Group__0__Impl rule__Comparison__Group__1
            {
            pushFollow(FOLLOW_48);
            rule__Comparison__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Comparison__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group__0"


    // $ANTLR start "rule__Comparison__Group__0__Impl"
    // InternalMiniJava.g:5429:1: rule__Comparison__Group__0__Impl : ( rulePlusOrMinus ) ;
    public final void rule__Comparison__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5433:1: ( ( rulePlusOrMinus ) )
            // InternalMiniJava.g:5434:1: ( rulePlusOrMinus )
            {
            // InternalMiniJava.g:5434:1: ( rulePlusOrMinus )
            // InternalMiniJava.g:5435:2: rulePlusOrMinus
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getComparisonAccess().getPlusOrMinusParserRuleCall_0()); 
            }
            pushFollow(FOLLOW_2);
            rulePlusOrMinus();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getComparisonAccess().getPlusOrMinusParserRuleCall_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group__0__Impl"


    // $ANTLR start "rule__Comparison__Group__1"
    // InternalMiniJava.g:5444:1: rule__Comparison__Group__1 : rule__Comparison__Group__1__Impl ;
    public final void rule__Comparison__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5448:1: ( rule__Comparison__Group__1__Impl )
            // InternalMiniJava.g:5449:2: rule__Comparison__Group__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Comparison__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group__1"


    // $ANTLR start "rule__Comparison__Group__1__Impl"
    // InternalMiniJava.g:5455:1: rule__Comparison__Group__1__Impl : ( ( rule__Comparison__Group_1__0 )* ) ;
    public final void rule__Comparison__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5459:1: ( ( ( rule__Comparison__Group_1__0 )* ) )
            // InternalMiniJava.g:5460:1: ( ( rule__Comparison__Group_1__0 )* )
            {
            // InternalMiniJava.g:5460:1: ( ( rule__Comparison__Group_1__0 )* )
            // InternalMiniJava.g:5461:2: ( rule__Comparison__Group_1__0 )*
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getComparisonAccess().getGroup_1()); 
            }
            // InternalMiniJava.g:5462:2: ( rule__Comparison__Group_1__0 )*
            loop47:
            do {
                int alt47=2;
                int LA47_0 = input.LA(1);

                if ( ((LA47_0>=49 && LA47_0<=52)) ) {
                    alt47=1;
                }


                switch (alt47) {
            	case 1 :
            	    // InternalMiniJava.g:5462:3: rule__Comparison__Group_1__0
            	    {
            	    pushFollow(FOLLOW_49);
            	    rule__Comparison__Group_1__0();

            	    state._fsp--;
            	    if (state.failed) return ;

            	    }
            	    break;

            	default :
            	    break loop47;
                }
            } while (true);

            if ( state.backtracking==0 ) {
               after(grammarAccess.getComparisonAccess().getGroup_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group__1__Impl"


    // $ANTLR start "rule__Comparison__Group_1__0"
    // InternalMiniJava.g:5471:1: rule__Comparison__Group_1__0 : rule__Comparison__Group_1__0__Impl rule__Comparison__Group_1__1 ;
    public final void rule__Comparison__Group_1__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5475:1: ( rule__Comparison__Group_1__0__Impl rule__Comparison__Group_1__1 )
            // InternalMiniJava.g:5476:2: rule__Comparison__Group_1__0__Impl rule__Comparison__Group_1__1
            {
            pushFollow(FOLLOW_25);
            rule__Comparison__Group_1__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Comparison__Group_1__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group_1__0"


    // $ANTLR start "rule__Comparison__Group_1__0__Impl"
    // InternalMiniJava.g:5483:1: rule__Comparison__Group_1__0__Impl : ( ( rule__Comparison__Alternatives_1_0 ) ) ;
    public final void rule__Comparison__Group_1__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5487:1: ( ( ( rule__Comparison__Alternatives_1_0 ) ) )
            // InternalMiniJava.g:5488:1: ( ( rule__Comparison__Alternatives_1_0 ) )
            {
            // InternalMiniJava.g:5488:1: ( ( rule__Comparison__Alternatives_1_0 ) )
            // InternalMiniJava.g:5489:2: ( rule__Comparison__Alternatives_1_0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getComparisonAccess().getAlternatives_1_0()); 
            }
            // InternalMiniJava.g:5490:2: ( rule__Comparison__Alternatives_1_0 )
            // InternalMiniJava.g:5490:3: rule__Comparison__Alternatives_1_0
            {
            pushFollow(FOLLOW_2);
            rule__Comparison__Alternatives_1_0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getComparisonAccess().getAlternatives_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group_1__0__Impl"


    // $ANTLR start "rule__Comparison__Group_1__1"
    // InternalMiniJava.g:5498:1: rule__Comparison__Group_1__1 : rule__Comparison__Group_1__1__Impl ;
    public final void rule__Comparison__Group_1__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5502:1: ( rule__Comparison__Group_1__1__Impl )
            // InternalMiniJava.g:5503:2: rule__Comparison__Group_1__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Comparison__Group_1__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group_1__1"


    // $ANTLR start "rule__Comparison__Group_1__1__Impl"
    // InternalMiniJava.g:5509:1: rule__Comparison__Group_1__1__Impl : ( ( rule__Comparison__RightAssignment_1_1 ) ) ;
    public final void rule__Comparison__Group_1__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5513:1: ( ( ( rule__Comparison__RightAssignment_1_1 ) ) )
            // InternalMiniJava.g:5514:1: ( ( rule__Comparison__RightAssignment_1_1 ) )
            {
            // InternalMiniJava.g:5514:1: ( ( rule__Comparison__RightAssignment_1_1 ) )
            // InternalMiniJava.g:5515:2: ( rule__Comparison__RightAssignment_1_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getComparisonAccess().getRightAssignment_1_1()); 
            }
            // InternalMiniJava.g:5516:2: ( rule__Comparison__RightAssignment_1_1 )
            // InternalMiniJava.g:5516:3: rule__Comparison__RightAssignment_1_1
            {
            pushFollow(FOLLOW_2);
            rule__Comparison__RightAssignment_1_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getComparisonAccess().getRightAssignment_1_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group_1__1__Impl"


    // $ANTLR start "rule__Comparison__Group_1_0_0__0"
    // InternalMiniJava.g:5525:1: rule__Comparison__Group_1_0_0__0 : rule__Comparison__Group_1_0_0__0__Impl rule__Comparison__Group_1_0_0__1 ;
    public final void rule__Comparison__Group_1_0_0__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5529:1: ( rule__Comparison__Group_1_0_0__0__Impl rule__Comparison__Group_1_0_0__1 )
            // InternalMiniJava.g:5530:2: rule__Comparison__Group_1_0_0__0__Impl rule__Comparison__Group_1_0_0__1
            {
            pushFollow(FOLLOW_50);
            rule__Comparison__Group_1_0_0__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Comparison__Group_1_0_0__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group_1_0_0__0"


    // $ANTLR start "rule__Comparison__Group_1_0_0__0__Impl"
    // InternalMiniJava.g:5537:1: rule__Comparison__Group_1_0_0__0__Impl : ( () ) ;
    public final void rule__Comparison__Group_1_0_0__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5541:1: ( ( () ) )
            // InternalMiniJava.g:5542:1: ( () )
            {
            // InternalMiniJava.g:5542:1: ( () )
            // InternalMiniJava.g:5543:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getComparisonAccess().getSuperiorOrEqualLeftAction_1_0_0_0()); 
            }
            // InternalMiniJava.g:5544:2: ()
            // InternalMiniJava.g:5544:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getComparisonAccess().getSuperiorOrEqualLeftAction_1_0_0_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group_1_0_0__0__Impl"


    // $ANTLR start "rule__Comparison__Group_1_0_0__1"
    // InternalMiniJava.g:5552:1: rule__Comparison__Group_1_0_0__1 : rule__Comparison__Group_1_0_0__1__Impl ;
    public final void rule__Comparison__Group_1_0_0__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5556:1: ( rule__Comparison__Group_1_0_0__1__Impl )
            // InternalMiniJava.g:5557:2: rule__Comparison__Group_1_0_0__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Comparison__Group_1_0_0__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group_1_0_0__1"


    // $ANTLR start "rule__Comparison__Group_1_0_0__1__Impl"
    // InternalMiniJava.g:5563:1: rule__Comparison__Group_1_0_0__1__Impl : ( '>=' ) ;
    public final void rule__Comparison__Group_1_0_0__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5567:1: ( ( '>=' ) )
            // InternalMiniJava.g:5568:1: ( '>=' )
            {
            // InternalMiniJava.g:5568:1: ( '>=' )
            // InternalMiniJava.g:5569:2: '>='
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getComparisonAccess().getGreaterThanSignEqualsSignKeyword_1_0_0_1()); 
            }
            match(input,49,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getComparisonAccess().getGreaterThanSignEqualsSignKeyword_1_0_0_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group_1_0_0__1__Impl"


    // $ANTLR start "rule__Comparison__Group_1_0_1__0"
    // InternalMiniJava.g:5579:1: rule__Comparison__Group_1_0_1__0 : rule__Comparison__Group_1_0_1__0__Impl rule__Comparison__Group_1_0_1__1 ;
    public final void rule__Comparison__Group_1_0_1__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5583:1: ( rule__Comparison__Group_1_0_1__0__Impl rule__Comparison__Group_1_0_1__1 )
            // InternalMiniJava.g:5584:2: rule__Comparison__Group_1_0_1__0__Impl rule__Comparison__Group_1_0_1__1
            {
            pushFollow(FOLLOW_51);
            rule__Comparison__Group_1_0_1__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Comparison__Group_1_0_1__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group_1_0_1__0"


    // $ANTLR start "rule__Comparison__Group_1_0_1__0__Impl"
    // InternalMiniJava.g:5591:1: rule__Comparison__Group_1_0_1__0__Impl : ( () ) ;
    public final void rule__Comparison__Group_1_0_1__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5595:1: ( ( () ) )
            // InternalMiniJava.g:5596:1: ( () )
            {
            // InternalMiniJava.g:5596:1: ( () )
            // InternalMiniJava.g:5597:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getComparisonAccess().getInferiorOrEqualLeftAction_1_0_1_0()); 
            }
            // InternalMiniJava.g:5598:2: ()
            // InternalMiniJava.g:5598:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getComparisonAccess().getInferiorOrEqualLeftAction_1_0_1_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group_1_0_1__0__Impl"


    // $ANTLR start "rule__Comparison__Group_1_0_1__1"
    // InternalMiniJava.g:5606:1: rule__Comparison__Group_1_0_1__1 : rule__Comparison__Group_1_0_1__1__Impl ;
    public final void rule__Comparison__Group_1_0_1__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5610:1: ( rule__Comparison__Group_1_0_1__1__Impl )
            // InternalMiniJava.g:5611:2: rule__Comparison__Group_1_0_1__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Comparison__Group_1_0_1__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group_1_0_1__1"


    // $ANTLR start "rule__Comparison__Group_1_0_1__1__Impl"
    // InternalMiniJava.g:5617:1: rule__Comparison__Group_1_0_1__1__Impl : ( '<=' ) ;
    public final void rule__Comparison__Group_1_0_1__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5621:1: ( ( '<=' ) )
            // InternalMiniJava.g:5622:1: ( '<=' )
            {
            // InternalMiniJava.g:5622:1: ( '<=' )
            // InternalMiniJava.g:5623:2: '<='
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getComparisonAccess().getLessThanSignEqualsSignKeyword_1_0_1_1()); 
            }
            match(input,50,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getComparisonAccess().getLessThanSignEqualsSignKeyword_1_0_1_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group_1_0_1__1__Impl"


    // $ANTLR start "rule__Comparison__Group_1_0_2__0"
    // InternalMiniJava.g:5633:1: rule__Comparison__Group_1_0_2__0 : rule__Comparison__Group_1_0_2__0__Impl rule__Comparison__Group_1_0_2__1 ;
    public final void rule__Comparison__Group_1_0_2__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5637:1: ( rule__Comparison__Group_1_0_2__0__Impl rule__Comparison__Group_1_0_2__1 )
            // InternalMiniJava.g:5638:2: rule__Comparison__Group_1_0_2__0__Impl rule__Comparison__Group_1_0_2__1
            {
            pushFollow(FOLLOW_52);
            rule__Comparison__Group_1_0_2__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Comparison__Group_1_0_2__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group_1_0_2__0"


    // $ANTLR start "rule__Comparison__Group_1_0_2__0__Impl"
    // InternalMiniJava.g:5645:1: rule__Comparison__Group_1_0_2__0__Impl : ( () ) ;
    public final void rule__Comparison__Group_1_0_2__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5649:1: ( ( () ) )
            // InternalMiniJava.g:5650:1: ( () )
            {
            // InternalMiniJava.g:5650:1: ( () )
            // InternalMiniJava.g:5651:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getComparisonAccess().getSuperiorLeftAction_1_0_2_0()); 
            }
            // InternalMiniJava.g:5652:2: ()
            // InternalMiniJava.g:5652:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getComparisonAccess().getSuperiorLeftAction_1_0_2_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group_1_0_2__0__Impl"


    // $ANTLR start "rule__Comparison__Group_1_0_2__1"
    // InternalMiniJava.g:5660:1: rule__Comparison__Group_1_0_2__1 : rule__Comparison__Group_1_0_2__1__Impl ;
    public final void rule__Comparison__Group_1_0_2__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5664:1: ( rule__Comparison__Group_1_0_2__1__Impl )
            // InternalMiniJava.g:5665:2: rule__Comparison__Group_1_0_2__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Comparison__Group_1_0_2__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group_1_0_2__1"


    // $ANTLR start "rule__Comparison__Group_1_0_2__1__Impl"
    // InternalMiniJava.g:5671:1: rule__Comparison__Group_1_0_2__1__Impl : ( '>' ) ;
    public final void rule__Comparison__Group_1_0_2__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5675:1: ( ( '>' ) )
            // InternalMiniJava.g:5676:1: ( '>' )
            {
            // InternalMiniJava.g:5676:1: ( '>' )
            // InternalMiniJava.g:5677:2: '>'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getComparisonAccess().getGreaterThanSignKeyword_1_0_2_1()); 
            }
            match(input,51,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getComparisonAccess().getGreaterThanSignKeyword_1_0_2_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group_1_0_2__1__Impl"


    // $ANTLR start "rule__Comparison__Group_1_0_3__0"
    // InternalMiniJava.g:5687:1: rule__Comparison__Group_1_0_3__0 : rule__Comparison__Group_1_0_3__0__Impl rule__Comparison__Group_1_0_3__1 ;
    public final void rule__Comparison__Group_1_0_3__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5691:1: ( rule__Comparison__Group_1_0_3__0__Impl rule__Comparison__Group_1_0_3__1 )
            // InternalMiniJava.g:5692:2: rule__Comparison__Group_1_0_3__0__Impl rule__Comparison__Group_1_0_3__1
            {
            pushFollow(FOLLOW_48);
            rule__Comparison__Group_1_0_3__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Comparison__Group_1_0_3__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group_1_0_3__0"


    // $ANTLR start "rule__Comparison__Group_1_0_3__0__Impl"
    // InternalMiniJava.g:5699:1: rule__Comparison__Group_1_0_3__0__Impl : ( () ) ;
    public final void rule__Comparison__Group_1_0_3__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5703:1: ( ( () ) )
            // InternalMiniJava.g:5704:1: ( () )
            {
            // InternalMiniJava.g:5704:1: ( () )
            // InternalMiniJava.g:5705:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getComparisonAccess().getInferiorLeftAction_1_0_3_0()); 
            }
            // InternalMiniJava.g:5706:2: ()
            // InternalMiniJava.g:5706:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getComparisonAccess().getInferiorLeftAction_1_0_3_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group_1_0_3__0__Impl"


    // $ANTLR start "rule__Comparison__Group_1_0_3__1"
    // InternalMiniJava.g:5714:1: rule__Comparison__Group_1_0_3__1 : rule__Comparison__Group_1_0_3__1__Impl ;
    public final void rule__Comparison__Group_1_0_3__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5718:1: ( rule__Comparison__Group_1_0_3__1__Impl )
            // InternalMiniJava.g:5719:2: rule__Comparison__Group_1_0_3__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Comparison__Group_1_0_3__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group_1_0_3__1"


    // $ANTLR start "rule__Comparison__Group_1_0_3__1__Impl"
    // InternalMiniJava.g:5725:1: rule__Comparison__Group_1_0_3__1__Impl : ( '<' ) ;
    public final void rule__Comparison__Group_1_0_3__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5729:1: ( ( '<' ) )
            // InternalMiniJava.g:5730:1: ( '<' )
            {
            // InternalMiniJava.g:5730:1: ( '<' )
            // InternalMiniJava.g:5731:2: '<'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getComparisonAccess().getLessThanSignKeyword_1_0_3_1()); 
            }
            match(input,52,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getComparisonAccess().getLessThanSignKeyword_1_0_3_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__Group_1_0_3__1__Impl"


    // $ANTLR start "rule__PlusOrMinus__Group__0"
    // InternalMiniJava.g:5741:1: rule__PlusOrMinus__Group__0 : rule__PlusOrMinus__Group__0__Impl rule__PlusOrMinus__Group__1 ;
    public final void rule__PlusOrMinus__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5745:1: ( rule__PlusOrMinus__Group__0__Impl rule__PlusOrMinus__Group__1 )
            // InternalMiniJava.g:5746:2: rule__PlusOrMinus__Group__0__Impl rule__PlusOrMinus__Group__1
            {
            pushFollow(FOLLOW_53);
            rule__PlusOrMinus__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__PlusOrMinus__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PlusOrMinus__Group__0"


    // $ANTLR start "rule__PlusOrMinus__Group__0__Impl"
    // InternalMiniJava.g:5753:1: rule__PlusOrMinus__Group__0__Impl : ( ruleMulOrDiv ) ;
    public final void rule__PlusOrMinus__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5757:1: ( ( ruleMulOrDiv ) )
            // InternalMiniJava.g:5758:1: ( ruleMulOrDiv )
            {
            // InternalMiniJava.g:5758:1: ( ruleMulOrDiv )
            // InternalMiniJava.g:5759:2: ruleMulOrDiv
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPlusOrMinusAccess().getMulOrDivParserRuleCall_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleMulOrDiv();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getPlusOrMinusAccess().getMulOrDivParserRuleCall_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PlusOrMinus__Group__0__Impl"


    // $ANTLR start "rule__PlusOrMinus__Group__1"
    // InternalMiniJava.g:5768:1: rule__PlusOrMinus__Group__1 : rule__PlusOrMinus__Group__1__Impl ;
    public final void rule__PlusOrMinus__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5772:1: ( rule__PlusOrMinus__Group__1__Impl )
            // InternalMiniJava.g:5773:2: rule__PlusOrMinus__Group__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__PlusOrMinus__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PlusOrMinus__Group__1"


    // $ANTLR start "rule__PlusOrMinus__Group__1__Impl"
    // InternalMiniJava.g:5779:1: rule__PlusOrMinus__Group__1__Impl : ( ( rule__PlusOrMinus__Group_1__0 )* ) ;
    public final void rule__PlusOrMinus__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5783:1: ( ( ( rule__PlusOrMinus__Group_1__0 )* ) )
            // InternalMiniJava.g:5784:1: ( ( rule__PlusOrMinus__Group_1__0 )* )
            {
            // InternalMiniJava.g:5784:1: ( ( rule__PlusOrMinus__Group_1__0 )* )
            // InternalMiniJava.g:5785:2: ( rule__PlusOrMinus__Group_1__0 )*
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPlusOrMinusAccess().getGroup_1()); 
            }
            // InternalMiniJava.g:5786:2: ( rule__PlusOrMinus__Group_1__0 )*
            loop48:
            do {
                int alt48=2;
                int LA48_0 = input.LA(1);

                if ( ((LA48_0>=53 && LA48_0<=54)) ) {
                    alt48=1;
                }


                switch (alt48) {
            	case 1 :
            	    // InternalMiniJava.g:5786:3: rule__PlusOrMinus__Group_1__0
            	    {
            	    pushFollow(FOLLOW_54);
            	    rule__PlusOrMinus__Group_1__0();

            	    state._fsp--;
            	    if (state.failed) return ;

            	    }
            	    break;

            	default :
            	    break loop48;
                }
            } while (true);

            if ( state.backtracking==0 ) {
               after(grammarAccess.getPlusOrMinusAccess().getGroup_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PlusOrMinus__Group__1__Impl"


    // $ANTLR start "rule__PlusOrMinus__Group_1__0"
    // InternalMiniJava.g:5795:1: rule__PlusOrMinus__Group_1__0 : rule__PlusOrMinus__Group_1__0__Impl rule__PlusOrMinus__Group_1__1 ;
    public final void rule__PlusOrMinus__Group_1__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5799:1: ( rule__PlusOrMinus__Group_1__0__Impl rule__PlusOrMinus__Group_1__1 )
            // InternalMiniJava.g:5800:2: rule__PlusOrMinus__Group_1__0__Impl rule__PlusOrMinus__Group_1__1
            {
            pushFollow(FOLLOW_25);
            rule__PlusOrMinus__Group_1__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__PlusOrMinus__Group_1__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PlusOrMinus__Group_1__0"


    // $ANTLR start "rule__PlusOrMinus__Group_1__0__Impl"
    // InternalMiniJava.g:5807:1: rule__PlusOrMinus__Group_1__0__Impl : ( ( rule__PlusOrMinus__Alternatives_1_0 ) ) ;
    public final void rule__PlusOrMinus__Group_1__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5811:1: ( ( ( rule__PlusOrMinus__Alternatives_1_0 ) ) )
            // InternalMiniJava.g:5812:1: ( ( rule__PlusOrMinus__Alternatives_1_0 ) )
            {
            // InternalMiniJava.g:5812:1: ( ( rule__PlusOrMinus__Alternatives_1_0 ) )
            // InternalMiniJava.g:5813:2: ( rule__PlusOrMinus__Alternatives_1_0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPlusOrMinusAccess().getAlternatives_1_0()); 
            }
            // InternalMiniJava.g:5814:2: ( rule__PlusOrMinus__Alternatives_1_0 )
            // InternalMiniJava.g:5814:3: rule__PlusOrMinus__Alternatives_1_0
            {
            pushFollow(FOLLOW_2);
            rule__PlusOrMinus__Alternatives_1_0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getPlusOrMinusAccess().getAlternatives_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PlusOrMinus__Group_1__0__Impl"


    // $ANTLR start "rule__PlusOrMinus__Group_1__1"
    // InternalMiniJava.g:5822:1: rule__PlusOrMinus__Group_1__1 : rule__PlusOrMinus__Group_1__1__Impl ;
    public final void rule__PlusOrMinus__Group_1__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5826:1: ( rule__PlusOrMinus__Group_1__1__Impl )
            // InternalMiniJava.g:5827:2: rule__PlusOrMinus__Group_1__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__PlusOrMinus__Group_1__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PlusOrMinus__Group_1__1"


    // $ANTLR start "rule__PlusOrMinus__Group_1__1__Impl"
    // InternalMiniJava.g:5833:1: rule__PlusOrMinus__Group_1__1__Impl : ( ( rule__PlusOrMinus__RightAssignment_1_1 ) ) ;
    public final void rule__PlusOrMinus__Group_1__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5837:1: ( ( ( rule__PlusOrMinus__RightAssignment_1_1 ) ) )
            // InternalMiniJava.g:5838:1: ( ( rule__PlusOrMinus__RightAssignment_1_1 ) )
            {
            // InternalMiniJava.g:5838:1: ( ( rule__PlusOrMinus__RightAssignment_1_1 ) )
            // InternalMiniJava.g:5839:2: ( rule__PlusOrMinus__RightAssignment_1_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPlusOrMinusAccess().getRightAssignment_1_1()); 
            }
            // InternalMiniJava.g:5840:2: ( rule__PlusOrMinus__RightAssignment_1_1 )
            // InternalMiniJava.g:5840:3: rule__PlusOrMinus__RightAssignment_1_1
            {
            pushFollow(FOLLOW_2);
            rule__PlusOrMinus__RightAssignment_1_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getPlusOrMinusAccess().getRightAssignment_1_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PlusOrMinus__Group_1__1__Impl"


    // $ANTLR start "rule__PlusOrMinus__Group_1_0_0__0"
    // InternalMiniJava.g:5849:1: rule__PlusOrMinus__Group_1_0_0__0 : rule__PlusOrMinus__Group_1_0_0__0__Impl rule__PlusOrMinus__Group_1_0_0__1 ;
    public final void rule__PlusOrMinus__Group_1_0_0__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5853:1: ( rule__PlusOrMinus__Group_1_0_0__0__Impl rule__PlusOrMinus__Group_1_0_0__1 )
            // InternalMiniJava.g:5854:2: rule__PlusOrMinus__Group_1_0_0__0__Impl rule__PlusOrMinus__Group_1_0_0__1
            {
            pushFollow(FOLLOW_55);
            rule__PlusOrMinus__Group_1_0_0__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__PlusOrMinus__Group_1_0_0__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PlusOrMinus__Group_1_0_0__0"


    // $ANTLR start "rule__PlusOrMinus__Group_1_0_0__0__Impl"
    // InternalMiniJava.g:5861:1: rule__PlusOrMinus__Group_1_0_0__0__Impl : ( () ) ;
    public final void rule__PlusOrMinus__Group_1_0_0__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5865:1: ( ( () ) )
            // InternalMiniJava.g:5866:1: ( () )
            {
            // InternalMiniJava.g:5866:1: ( () )
            // InternalMiniJava.g:5867:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPlusOrMinusAccess().getPlusLeftAction_1_0_0_0()); 
            }
            // InternalMiniJava.g:5868:2: ()
            // InternalMiniJava.g:5868:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getPlusOrMinusAccess().getPlusLeftAction_1_0_0_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PlusOrMinus__Group_1_0_0__0__Impl"


    // $ANTLR start "rule__PlusOrMinus__Group_1_0_0__1"
    // InternalMiniJava.g:5876:1: rule__PlusOrMinus__Group_1_0_0__1 : rule__PlusOrMinus__Group_1_0_0__1__Impl ;
    public final void rule__PlusOrMinus__Group_1_0_0__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5880:1: ( rule__PlusOrMinus__Group_1_0_0__1__Impl )
            // InternalMiniJava.g:5881:2: rule__PlusOrMinus__Group_1_0_0__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__PlusOrMinus__Group_1_0_0__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PlusOrMinus__Group_1_0_0__1"


    // $ANTLR start "rule__PlusOrMinus__Group_1_0_0__1__Impl"
    // InternalMiniJava.g:5887:1: rule__PlusOrMinus__Group_1_0_0__1__Impl : ( '+' ) ;
    public final void rule__PlusOrMinus__Group_1_0_0__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5891:1: ( ( '+' ) )
            // InternalMiniJava.g:5892:1: ( '+' )
            {
            // InternalMiniJava.g:5892:1: ( '+' )
            // InternalMiniJava.g:5893:2: '+'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPlusOrMinusAccess().getPlusSignKeyword_1_0_0_1()); 
            }
            match(input,53,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getPlusOrMinusAccess().getPlusSignKeyword_1_0_0_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PlusOrMinus__Group_1_0_0__1__Impl"


    // $ANTLR start "rule__PlusOrMinus__Group_1_0_1__0"
    // InternalMiniJava.g:5903:1: rule__PlusOrMinus__Group_1_0_1__0 : rule__PlusOrMinus__Group_1_0_1__0__Impl rule__PlusOrMinus__Group_1_0_1__1 ;
    public final void rule__PlusOrMinus__Group_1_0_1__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5907:1: ( rule__PlusOrMinus__Group_1_0_1__0__Impl rule__PlusOrMinus__Group_1_0_1__1 )
            // InternalMiniJava.g:5908:2: rule__PlusOrMinus__Group_1_0_1__0__Impl rule__PlusOrMinus__Group_1_0_1__1
            {
            pushFollow(FOLLOW_53);
            rule__PlusOrMinus__Group_1_0_1__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__PlusOrMinus__Group_1_0_1__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PlusOrMinus__Group_1_0_1__0"


    // $ANTLR start "rule__PlusOrMinus__Group_1_0_1__0__Impl"
    // InternalMiniJava.g:5915:1: rule__PlusOrMinus__Group_1_0_1__0__Impl : ( () ) ;
    public final void rule__PlusOrMinus__Group_1_0_1__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5919:1: ( ( () ) )
            // InternalMiniJava.g:5920:1: ( () )
            {
            // InternalMiniJava.g:5920:1: ( () )
            // InternalMiniJava.g:5921:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPlusOrMinusAccess().getMinusLeftAction_1_0_1_0()); 
            }
            // InternalMiniJava.g:5922:2: ()
            // InternalMiniJava.g:5922:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getPlusOrMinusAccess().getMinusLeftAction_1_0_1_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PlusOrMinus__Group_1_0_1__0__Impl"


    // $ANTLR start "rule__PlusOrMinus__Group_1_0_1__1"
    // InternalMiniJava.g:5930:1: rule__PlusOrMinus__Group_1_0_1__1 : rule__PlusOrMinus__Group_1_0_1__1__Impl ;
    public final void rule__PlusOrMinus__Group_1_0_1__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5934:1: ( rule__PlusOrMinus__Group_1_0_1__1__Impl )
            // InternalMiniJava.g:5935:2: rule__PlusOrMinus__Group_1_0_1__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__PlusOrMinus__Group_1_0_1__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PlusOrMinus__Group_1_0_1__1"


    // $ANTLR start "rule__PlusOrMinus__Group_1_0_1__1__Impl"
    // InternalMiniJava.g:5941:1: rule__PlusOrMinus__Group_1_0_1__1__Impl : ( '-' ) ;
    public final void rule__PlusOrMinus__Group_1_0_1__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5945:1: ( ( '-' ) )
            // InternalMiniJava.g:5946:1: ( '-' )
            {
            // InternalMiniJava.g:5946:1: ( '-' )
            // InternalMiniJava.g:5947:2: '-'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPlusOrMinusAccess().getHyphenMinusKeyword_1_0_1_1()); 
            }
            match(input,54,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getPlusOrMinusAccess().getHyphenMinusKeyword_1_0_1_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PlusOrMinus__Group_1_0_1__1__Impl"


    // $ANTLR start "rule__MulOrDiv__Group__0"
    // InternalMiniJava.g:5957:1: rule__MulOrDiv__Group__0 : rule__MulOrDiv__Group__0__Impl rule__MulOrDiv__Group__1 ;
    public final void rule__MulOrDiv__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5961:1: ( rule__MulOrDiv__Group__0__Impl rule__MulOrDiv__Group__1 )
            // InternalMiniJava.g:5962:2: rule__MulOrDiv__Group__0__Impl rule__MulOrDiv__Group__1
            {
            pushFollow(FOLLOW_56);
            rule__MulOrDiv__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__MulOrDiv__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__MulOrDiv__Group__0"


    // $ANTLR start "rule__MulOrDiv__Group__0__Impl"
    // InternalMiniJava.g:5969:1: rule__MulOrDiv__Group__0__Impl : ( ruleArrayAccess ) ;
    public final void rule__MulOrDiv__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5973:1: ( ( ruleArrayAccess ) )
            // InternalMiniJava.g:5974:1: ( ruleArrayAccess )
            {
            // InternalMiniJava.g:5974:1: ( ruleArrayAccess )
            // InternalMiniJava.g:5975:2: ruleArrayAccess
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMulOrDivAccess().getArrayAccessParserRuleCall_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleArrayAccess();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getMulOrDivAccess().getArrayAccessParserRuleCall_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__MulOrDiv__Group__0__Impl"


    // $ANTLR start "rule__MulOrDiv__Group__1"
    // InternalMiniJava.g:5984:1: rule__MulOrDiv__Group__1 : rule__MulOrDiv__Group__1__Impl ;
    public final void rule__MulOrDiv__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5988:1: ( rule__MulOrDiv__Group__1__Impl )
            // InternalMiniJava.g:5989:2: rule__MulOrDiv__Group__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__MulOrDiv__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__MulOrDiv__Group__1"


    // $ANTLR start "rule__MulOrDiv__Group__1__Impl"
    // InternalMiniJava.g:5995:1: rule__MulOrDiv__Group__1__Impl : ( ( rule__MulOrDiv__Group_1__0 )* ) ;
    public final void rule__MulOrDiv__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:5999:1: ( ( ( rule__MulOrDiv__Group_1__0 )* ) )
            // InternalMiniJava.g:6000:1: ( ( rule__MulOrDiv__Group_1__0 )* )
            {
            // InternalMiniJava.g:6000:1: ( ( rule__MulOrDiv__Group_1__0 )* )
            // InternalMiniJava.g:6001:2: ( rule__MulOrDiv__Group_1__0 )*
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMulOrDivAccess().getGroup_1()); 
            }
            // InternalMiniJava.g:6002:2: ( rule__MulOrDiv__Group_1__0 )*
            loop49:
            do {
                int alt49=2;
                int LA49_0 = input.LA(1);

                if ( ((LA49_0>=55 && LA49_0<=56)) ) {
                    alt49=1;
                }


                switch (alt49) {
            	case 1 :
            	    // InternalMiniJava.g:6002:3: rule__MulOrDiv__Group_1__0
            	    {
            	    pushFollow(FOLLOW_57);
            	    rule__MulOrDiv__Group_1__0();

            	    state._fsp--;
            	    if (state.failed) return ;

            	    }
            	    break;

            	default :
            	    break loop49;
                }
            } while (true);

            if ( state.backtracking==0 ) {
               after(grammarAccess.getMulOrDivAccess().getGroup_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__MulOrDiv__Group__1__Impl"


    // $ANTLR start "rule__MulOrDiv__Group_1__0"
    // InternalMiniJava.g:6011:1: rule__MulOrDiv__Group_1__0 : rule__MulOrDiv__Group_1__0__Impl rule__MulOrDiv__Group_1__1 ;
    public final void rule__MulOrDiv__Group_1__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6015:1: ( rule__MulOrDiv__Group_1__0__Impl rule__MulOrDiv__Group_1__1 )
            // InternalMiniJava.g:6016:2: rule__MulOrDiv__Group_1__0__Impl rule__MulOrDiv__Group_1__1
            {
            pushFollow(FOLLOW_25);
            rule__MulOrDiv__Group_1__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__MulOrDiv__Group_1__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__MulOrDiv__Group_1__0"


    // $ANTLR start "rule__MulOrDiv__Group_1__0__Impl"
    // InternalMiniJava.g:6023:1: rule__MulOrDiv__Group_1__0__Impl : ( ( rule__MulOrDiv__Alternatives_1_0 ) ) ;
    public final void rule__MulOrDiv__Group_1__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6027:1: ( ( ( rule__MulOrDiv__Alternatives_1_0 ) ) )
            // InternalMiniJava.g:6028:1: ( ( rule__MulOrDiv__Alternatives_1_0 ) )
            {
            // InternalMiniJava.g:6028:1: ( ( rule__MulOrDiv__Alternatives_1_0 ) )
            // InternalMiniJava.g:6029:2: ( rule__MulOrDiv__Alternatives_1_0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMulOrDivAccess().getAlternatives_1_0()); 
            }
            // InternalMiniJava.g:6030:2: ( rule__MulOrDiv__Alternatives_1_0 )
            // InternalMiniJava.g:6030:3: rule__MulOrDiv__Alternatives_1_0
            {
            pushFollow(FOLLOW_2);
            rule__MulOrDiv__Alternatives_1_0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getMulOrDivAccess().getAlternatives_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__MulOrDiv__Group_1__0__Impl"


    // $ANTLR start "rule__MulOrDiv__Group_1__1"
    // InternalMiniJava.g:6038:1: rule__MulOrDiv__Group_1__1 : rule__MulOrDiv__Group_1__1__Impl ;
    public final void rule__MulOrDiv__Group_1__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6042:1: ( rule__MulOrDiv__Group_1__1__Impl )
            // InternalMiniJava.g:6043:2: rule__MulOrDiv__Group_1__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__MulOrDiv__Group_1__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__MulOrDiv__Group_1__1"


    // $ANTLR start "rule__MulOrDiv__Group_1__1__Impl"
    // InternalMiniJava.g:6049:1: rule__MulOrDiv__Group_1__1__Impl : ( ( rule__MulOrDiv__RightAssignment_1_1 ) ) ;
    public final void rule__MulOrDiv__Group_1__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6053:1: ( ( ( rule__MulOrDiv__RightAssignment_1_1 ) ) )
            // InternalMiniJava.g:6054:1: ( ( rule__MulOrDiv__RightAssignment_1_1 ) )
            {
            // InternalMiniJava.g:6054:1: ( ( rule__MulOrDiv__RightAssignment_1_1 ) )
            // InternalMiniJava.g:6055:2: ( rule__MulOrDiv__RightAssignment_1_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMulOrDivAccess().getRightAssignment_1_1()); 
            }
            // InternalMiniJava.g:6056:2: ( rule__MulOrDiv__RightAssignment_1_1 )
            // InternalMiniJava.g:6056:3: rule__MulOrDiv__RightAssignment_1_1
            {
            pushFollow(FOLLOW_2);
            rule__MulOrDiv__RightAssignment_1_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getMulOrDivAccess().getRightAssignment_1_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__MulOrDiv__Group_1__1__Impl"


    // $ANTLR start "rule__MulOrDiv__Group_1_0_0__0"
    // InternalMiniJava.g:6065:1: rule__MulOrDiv__Group_1_0_0__0 : rule__MulOrDiv__Group_1_0_0__0__Impl rule__MulOrDiv__Group_1_0_0__1 ;
    public final void rule__MulOrDiv__Group_1_0_0__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6069:1: ( rule__MulOrDiv__Group_1_0_0__0__Impl rule__MulOrDiv__Group_1_0_0__1 )
            // InternalMiniJava.g:6070:2: rule__MulOrDiv__Group_1_0_0__0__Impl rule__MulOrDiv__Group_1_0_0__1
            {
            pushFollow(FOLLOW_58);
            rule__MulOrDiv__Group_1_0_0__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__MulOrDiv__Group_1_0_0__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__MulOrDiv__Group_1_0_0__0"


    // $ANTLR start "rule__MulOrDiv__Group_1_0_0__0__Impl"
    // InternalMiniJava.g:6077:1: rule__MulOrDiv__Group_1_0_0__0__Impl : ( () ) ;
    public final void rule__MulOrDiv__Group_1_0_0__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6081:1: ( ( () ) )
            // InternalMiniJava.g:6082:1: ( () )
            {
            // InternalMiniJava.g:6082:1: ( () )
            // InternalMiniJava.g:6083:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMulOrDivAccess().getMultiplicationLeftAction_1_0_0_0()); 
            }
            // InternalMiniJava.g:6084:2: ()
            // InternalMiniJava.g:6084:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getMulOrDivAccess().getMultiplicationLeftAction_1_0_0_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__MulOrDiv__Group_1_0_0__0__Impl"


    // $ANTLR start "rule__MulOrDiv__Group_1_0_0__1"
    // InternalMiniJava.g:6092:1: rule__MulOrDiv__Group_1_0_0__1 : rule__MulOrDiv__Group_1_0_0__1__Impl ;
    public final void rule__MulOrDiv__Group_1_0_0__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6096:1: ( rule__MulOrDiv__Group_1_0_0__1__Impl )
            // InternalMiniJava.g:6097:2: rule__MulOrDiv__Group_1_0_0__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__MulOrDiv__Group_1_0_0__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__MulOrDiv__Group_1_0_0__1"


    // $ANTLR start "rule__MulOrDiv__Group_1_0_0__1__Impl"
    // InternalMiniJava.g:6103:1: rule__MulOrDiv__Group_1_0_0__1__Impl : ( '*' ) ;
    public final void rule__MulOrDiv__Group_1_0_0__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6107:1: ( ( '*' ) )
            // InternalMiniJava.g:6108:1: ( '*' )
            {
            // InternalMiniJava.g:6108:1: ( '*' )
            // InternalMiniJava.g:6109:2: '*'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMulOrDivAccess().getAsteriskKeyword_1_0_0_1()); 
            }
            match(input,55,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getMulOrDivAccess().getAsteriskKeyword_1_0_0_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__MulOrDiv__Group_1_0_0__1__Impl"


    // $ANTLR start "rule__MulOrDiv__Group_1_0_1__0"
    // InternalMiniJava.g:6119:1: rule__MulOrDiv__Group_1_0_1__0 : rule__MulOrDiv__Group_1_0_1__0__Impl rule__MulOrDiv__Group_1_0_1__1 ;
    public final void rule__MulOrDiv__Group_1_0_1__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6123:1: ( rule__MulOrDiv__Group_1_0_1__0__Impl rule__MulOrDiv__Group_1_0_1__1 )
            // InternalMiniJava.g:6124:2: rule__MulOrDiv__Group_1_0_1__0__Impl rule__MulOrDiv__Group_1_0_1__1
            {
            pushFollow(FOLLOW_56);
            rule__MulOrDiv__Group_1_0_1__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__MulOrDiv__Group_1_0_1__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__MulOrDiv__Group_1_0_1__0"


    // $ANTLR start "rule__MulOrDiv__Group_1_0_1__0__Impl"
    // InternalMiniJava.g:6131:1: rule__MulOrDiv__Group_1_0_1__0__Impl : ( () ) ;
    public final void rule__MulOrDiv__Group_1_0_1__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6135:1: ( ( () ) )
            // InternalMiniJava.g:6136:1: ( () )
            {
            // InternalMiniJava.g:6136:1: ( () )
            // InternalMiniJava.g:6137:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMulOrDivAccess().getDivisionLeftAction_1_0_1_0()); 
            }
            // InternalMiniJava.g:6138:2: ()
            // InternalMiniJava.g:6138:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getMulOrDivAccess().getDivisionLeftAction_1_0_1_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__MulOrDiv__Group_1_0_1__0__Impl"


    // $ANTLR start "rule__MulOrDiv__Group_1_0_1__1"
    // InternalMiniJava.g:6146:1: rule__MulOrDiv__Group_1_0_1__1 : rule__MulOrDiv__Group_1_0_1__1__Impl ;
    public final void rule__MulOrDiv__Group_1_0_1__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6150:1: ( rule__MulOrDiv__Group_1_0_1__1__Impl )
            // InternalMiniJava.g:6151:2: rule__MulOrDiv__Group_1_0_1__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__MulOrDiv__Group_1_0_1__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__MulOrDiv__Group_1_0_1__1"


    // $ANTLR start "rule__MulOrDiv__Group_1_0_1__1__Impl"
    // InternalMiniJava.g:6157:1: rule__MulOrDiv__Group_1_0_1__1__Impl : ( '/' ) ;
    public final void rule__MulOrDiv__Group_1_0_1__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6161:1: ( ( '/' ) )
            // InternalMiniJava.g:6162:1: ( '/' )
            {
            // InternalMiniJava.g:6162:1: ( '/' )
            // InternalMiniJava.g:6163:2: '/'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMulOrDivAccess().getSolidusKeyword_1_0_1_1()); 
            }
            match(input,56,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getMulOrDivAccess().getSolidusKeyword_1_0_1_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__MulOrDiv__Group_1_0_1__1__Impl"


    // $ANTLR start "rule__ArrayAccess__Group__0"
    // InternalMiniJava.g:6173:1: rule__ArrayAccess__Group__0 : rule__ArrayAccess__Group__0__Impl rule__ArrayAccess__Group__1 ;
    public final void rule__ArrayAccess__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6177:1: ( rule__ArrayAccess__Group__0__Impl rule__ArrayAccess__Group__1 )
            // InternalMiniJava.g:6178:2: rule__ArrayAccess__Group__0__Impl rule__ArrayAccess__Group__1
            {
            pushFollow(FOLLOW_35);
            rule__ArrayAccess__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__ArrayAccess__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayAccess__Group__0"


    // $ANTLR start "rule__ArrayAccess__Group__0__Impl"
    // InternalMiniJava.g:6185:1: rule__ArrayAccess__Group__0__Impl : ( ruleArrayLength ) ;
    public final void rule__ArrayAccess__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6189:1: ( ( ruleArrayLength ) )
            // InternalMiniJava.g:6190:1: ( ruleArrayLength )
            {
            // InternalMiniJava.g:6190:1: ( ruleArrayLength )
            // InternalMiniJava.g:6191:2: ruleArrayLength
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getArrayAccessAccess().getArrayLengthParserRuleCall_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleArrayLength();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getArrayAccessAccess().getArrayLengthParserRuleCall_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayAccess__Group__0__Impl"


    // $ANTLR start "rule__ArrayAccess__Group__1"
    // InternalMiniJava.g:6200:1: rule__ArrayAccess__Group__1 : rule__ArrayAccess__Group__1__Impl ;
    public final void rule__ArrayAccess__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6204:1: ( rule__ArrayAccess__Group__1__Impl )
            // InternalMiniJava.g:6205:2: rule__ArrayAccess__Group__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__ArrayAccess__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayAccess__Group__1"


    // $ANTLR start "rule__ArrayAccess__Group__1__Impl"
    // InternalMiniJava.g:6211:1: rule__ArrayAccess__Group__1__Impl : ( ( rule__ArrayAccess__Group_1__0 )? ) ;
    public final void rule__ArrayAccess__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6215:1: ( ( ( rule__ArrayAccess__Group_1__0 )? ) )
            // InternalMiniJava.g:6216:1: ( ( rule__ArrayAccess__Group_1__0 )? )
            {
            // InternalMiniJava.g:6216:1: ( ( rule__ArrayAccess__Group_1__0 )? )
            // InternalMiniJava.g:6217:2: ( rule__ArrayAccess__Group_1__0 )?
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getArrayAccessAccess().getGroup_1()); 
            }
            // InternalMiniJava.g:6218:2: ( rule__ArrayAccess__Group_1__0 )?
            int alt50=2;
            int LA50_0 = input.LA(1);

            if ( (LA50_0==39) ) {
                alt50=1;
            }
            switch (alt50) {
                case 1 :
                    // InternalMiniJava.g:6218:3: rule__ArrayAccess__Group_1__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__ArrayAccess__Group_1__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getArrayAccessAccess().getGroup_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayAccess__Group__1__Impl"


    // $ANTLR start "rule__ArrayAccess__Group_1__0"
    // InternalMiniJava.g:6227:1: rule__ArrayAccess__Group_1__0 : rule__ArrayAccess__Group_1__0__Impl rule__ArrayAccess__Group_1__1 ;
    public final void rule__ArrayAccess__Group_1__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6231:1: ( rule__ArrayAccess__Group_1__0__Impl rule__ArrayAccess__Group_1__1 )
            // InternalMiniJava.g:6232:2: rule__ArrayAccess__Group_1__0__Impl rule__ArrayAccess__Group_1__1
            {
            pushFollow(FOLLOW_35);
            rule__ArrayAccess__Group_1__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__ArrayAccess__Group_1__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayAccess__Group_1__0"


    // $ANTLR start "rule__ArrayAccess__Group_1__0__Impl"
    // InternalMiniJava.g:6239:1: rule__ArrayAccess__Group_1__0__Impl : ( () ) ;
    public final void rule__ArrayAccess__Group_1__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6243:1: ( ( () ) )
            // InternalMiniJava.g:6244:1: ( () )
            {
            // InternalMiniJava.g:6244:1: ( () )
            // InternalMiniJava.g:6245:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getArrayAccessAccess().getArrayAccessObjectAction_1_0()); 
            }
            // InternalMiniJava.g:6246:2: ()
            // InternalMiniJava.g:6246:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getArrayAccessAccess().getArrayAccessObjectAction_1_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayAccess__Group_1__0__Impl"


    // $ANTLR start "rule__ArrayAccess__Group_1__1"
    // InternalMiniJava.g:6254:1: rule__ArrayAccess__Group_1__1 : rule__ArrayAccess__Group_1__1__Impl rule__ArrayAccess__Group_1__2 ;
    public final void rule__ArrayAccess__Group_1__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6258:1: ( rule__ArrayAccess__Group_1__1__Impl rule__ArrayAccess__Group_1__2 )
            // InternalMiniJava.g:6259:2: rule__ArrayAccess__Group_1__1__Impl rule__ArrayAccess__Group_1__2
            {
            pushFollow(FOLLOW_25);
            rule__ArrayAccess__Group_1__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__ArrayAccess__Group_1__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayAccess__Group_1__1"


    // $ANTLR start "rule__ArrayAccess__Group_1__1__Impl"
    // InternalMiniJava.g:6266:1: rule__ArrayAccess__Group_1__1__Impl : ( '[' ) ;
    public final void rule__ArrayAccess__Group_1__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6270:1: ( ( '[' ) )
            // InternalMiniJava.g:6271:1: ( '[' )
            {
            // InternalMiniJava.g:6271:1: ( '[' )
            // InternalMiniJava.g:6272:2: '['
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getArrayAccessAccess().getLeftSquareBracketKeyword_1_1()); 
            }
            match(input,39,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getArrayAccessAccess().getLeftSquareBracketKeyword_1_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayAccess__Group_1__1__Impl"


    // $ANTLR start "rule__ArrayAccess__Group_1__2"
    // InternalMiniJava.g:6281:1: rule__ArrayAccess__Group_1__2 : rule__ArrayAccess__Group_1__2__Impl rule__ArrayAccess__Group_1__3 ;
    public final void rule__ArrayAccess__Group_1__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6285:1: ( rule__ArrayAccess__Group_1__2__Impl rule__ArrayAccess__Group_1__3 )
            // InternalMiniJava.g:6286:2: rule__ArrayAccess__Group_1__2__Impl rule__ArrayAccess__Group_1__3
            {
            pushFollow(FOLLOW_36);
            rule__ArrayAccess__Group_1__2__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__ArrayAccess__Group_1__3();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayAccess__Group_1__2"


    // $ANTLR start "rule__ArrayAccess__Group_1__2__Impl"
    // InternalMiniJava.g:6293:1: rule__ArrayAccess__Group_1__2__Impl : ( ( rule__ArrayAccess__IndexAssignment_1_2 ) ) ;
    public final void rule__ArrayAccess__Group_1__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6297:1: ( ( ( rule__ArrayAccess__IndexAssignment_1_2 ) ) )
            // InternalMiniJava.g:6298:1: ( ( rule__ArrayAccess__IndexAssignment_1_2 ) )
            {
            // InternalMiniJava.g:6298:1: ( ( rule__ArrayAccess__IndexAssignment_1_2 ) )
            // InternalMiniJava.g:6299:2: ( rule__ArrayAccess__IndexAssignment_1_2 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getArrayAccessAccess().getIndexAssignment_1_2()); 
            }
            // InternalMiniJava.g:6300:2: ( rule__ArrayAccess__IndexAssignment_1_2 )
            // InternalMiniJava.g:6300:3: rule__ArrayAccess__IndexAssignment_1_2
            {
            pushFollow(FOLLOW_2);
            rule__ArrayAccess__IndexAssignment_1_2();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getArrayAccessAccess().getIndexAssignment_1_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayAccess__Group_1__2__Impl"


    // $ANTLR start "rule__ArrayAccess__Group_1__3"
    // InternalMiniJava.g:6308:1: rule__ArrayAccess__Group_1__3 : rule__ArrayAccess__Group_1__3__Impl ;
    public final void rule__ArrayAccess__Group_1__3() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6312:1: ( rule__ArrayAccess__Group_1__3__Impl )
            // InternalMiniJava.g:6313:2: rule__ArrayAccess__Group_1__3__Impl
            {
            pushFollow(FOLLOW_2);
            rule__ArrayAccess__Group_1__3__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayAccess__Group_1__3"


    // $ANTLR start "rule__ArrayAccess__Group_1__3__Impl"
    // InternalMiniJava.g:6319:1: rule__ArrayAccess__Group_1__3__Impl : ( ']' ) ;
    public final void rule__ArrayAccess__Group_1__3__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6323:1: ( ( ']' ) )
            // InternalMiniJava.g:6324:1: ( ']' )
            {
            // InternalMiniJava.g:6324:1: ( ']' )
            // InternalMiniJava.g:6325:2: ']'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getArrayAccessAccess().getRightSquareBracketKeyword_1_3()); 
            }
            match(input,40,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getArrayAccessAccess().getRightSquareBracketKeyword_1_3()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayAccess__Group_1__3__Impl"


    // $ANTLR start "rule__ArrayLength__Group__0"
    // InternalMiniJava.g:6335:1: rule__ArrayLength__Group__0 : rule__ArrayLength__Group__0__Impl rule__ArrayLength__Group__1 ;
    public final void rule__ArrayLength__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6339:1: ( rule__ArrayLength__Group__0__Impl rule__ArrayLength__Group__1 )
            // InternalMiniJava.g:6340:2: rule__ArrayLength__Group__0__Impl rule__ArrayLength__Group__1
            {
            pushFollow(FOLLOW_8);
            rule__ArrayLength__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__ArrayLength__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayLength__Group__0"


    // $ANTLR start "rule__ArrayLength__Group__0__Impl"
    // InternalMiniJava.g:6347:1: rule__ArrayLength__Group__0__Impl : ( rulePrimary ) ;
    public final void rule__ArrayLength__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6351:1: ( ( rulePrimary ) )
            // InternalMiniJava.g:6352:1: ( rulePrimary )
            {
            // InternalMiniJava.g:6352:1: ( rulePrimary )
            // InternalMiniJava.g:6353:2: rulePrimary
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getArrayLengthAccess().getPrimaryParserRuleCall_0()); 
            }
            pushFollow(FOLLOW_2);
            rulePrimary();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getArrayLengthAccess().getPrimaryParserRuleCall_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayLength__Group__0__Impl"


    // $ANTLR start "rule__ArrayLength__Group__1"
    // InternalMiniJava.g:6362:1: rule__ArrayLength__Group__1 : rule__ArrayLength__Group__1__Impl ;
    public final void rule__ArrayLength__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6366:1: ( rule__ArrayLength__Group__1__Impl )
            // InternalMiniJava.g:6367:2: rule__ArrayLength__Group__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__ArrayLength__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayLength__Group__1"


    // $ANTLR start "rule__ArrayLength__Group__1__Impl"
    // InternalMiniJava.g:6373:1: rule__ArrayLength__Group__1__Impl : ( ( rule__ArrayLength__Group_1__0 )? ) ;
    public final void rule__ArrayLength__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6377:1: ( ( ( rule__ArrayLength__Group_1__0 )? ) )
            // InternalMiniJava.g:6378:1: ( ( rule__ArrayLength__Group_1__0 )? )
            {
            // InternalMiniJava.g:6378:1: ( ( rule__ArrayLength__Group_1__0 )? )
            // InternalMiniJava.g:6379:2: ( rule__ArrayLength__Group_1__0 )?
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getArrayLengthAccess().getGroup_1()); 
            }
            // InternalMiniJava.g:6380:2: ( rule__ArrayLength__Group_1__0 )?
            int alt51=2;
            int LA51_0 = input.LA(1);

            if ( (LA51_0==19) ) {
                alt51=1;
            }
            switch (alt51) {
                case 1 :
                    // InternalMiniJava.g:6380:3: rule__ArrayLength__Group_1__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__ArrayLength__Group_1__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getArrayLengthAccess().getGroup_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayLength__Group__1__Impl"


    // $ANTLR start "rule__ArrayLength__Group_1__0"
    // InternalMiniJava.g:6389:1: rule__ArrayLength__Group_1__0 : rule__ArrayLength__Group_1__0__Impl rule__ArrayLength__Group_1__1 ;
    public final void rule__ArrayLength__Group_1__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6393:1: ( rule__ArrayLength__Group_1__0__Impl rule__ArrayLength__Group_1__1 )
            // InternalMiniJava.g:6394:2: rule__ArrayLength__Group_1__0__Impl rule__ArrayLength__Group_1__1
            {
            pushFollow(FOLLOW_8);
            rule__ArrayLength__Group_1__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__ArrayLength__Group_1__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayLength__Group_1__0"


    // $ANTLR start "rule__ArrayLength__Group_1__0__Impl"
    // InternalMiniJava.g:6401:1: rule__ArrayLength__Group_1__0__Impl : ( () ) ;
    public final void rule__ArrayLength__Group_1__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6405:1: ( ( () ) )
            // InternalMiniJava.g:6406:1: ( () )
            {
            // InternalMiniJava.g:6406:1: ( () )
            // InternalMiniJava.g:6407:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getArrayLengthAccess().getArrayLengthArrayAction_1_0()); 
            }
            // InternalMiniJava.g:6408:2: ()
            // InternalMiniJava.g:6408:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getArrayLengthAccess().getArrayLengthArrayAction_1_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayLength__Group_1__0__Impl"


    // $ANTLR start "rule__ArrayLength__Group_1__1"
    // InternalMiniJava.g:6416:1: rule__ArrayLength__Group_1__1 : rule__ArrayLength__Group_1__1__Impl rule__ArrayLength__Group_1__2 ;
    public final void rule__ArrayLength__Group_1__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6420:1: ( rule__ArrayLength__Group_1__1__Impl rule__ArrayLength__Group_1__2 )
            // InternalMiniJava.g:6421:2: rule__ArrayLength__Group_1__1__Impl rule__ArrayLength__Group_1__2
            {
            pushFollow(FOLLOW_59);
            rule__ArrayLength__Group_1__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__ArrayLength__Group_1__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayLength__Group_1__1"


    // $ANTLR start "rule__ArrayLength__Group_1__1__Impl"
    // InternalMiniJava.g:6428:1: rule__ArrayLength__Group_1__1__Impl : ( '.' ) ;
    public final void rule__ArrayLength__Group_1__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6432:1: ( ( '.' ) )
            // InternalMiniJava.g:6433:1: ( '.' )
            {
            // InternalMiniJava.g:6433:1: ( '.' )
            // InternalMiniJava.g:6434:2: '.'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getArrayLengthAccess().getFullStopKeyword_1_1()); 
            }
            match(input,19,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getArrayLengthAccess().getFullStopKeyword_1_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayLength__Group_1__1__Impl"


    // $ANTLR start "rule__ArrayLength__Group_1__2"
    // InternalMiniJava.g:6443:1: rule__ArrayLength__Group_1__2 : rule__ArrayLength__Group_1__2__Impl ;
    public final void rule__ArrayLength__Group_1__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6447:1: ( rule__ArrayLength__Group_1__2__Impl )
            // InternalMiniJava.g:6448:2: rule__ArrayLength__Group_1__2__Impl
            {
            pushFollow(FOLLOW_2);
            rule__ArrayLength__Group_1__2__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayLength__Group_1__2"


    // $ANTLR start "rule__ArrayLength__Group_1__2__Impl"
    // InternalMiniJava.g:6454:1: rule__ArrayLength__Group_1__2__Impl : ( 'length' ) ;
    public final void rule__ArrayLength__Group_1__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6458:1: ( ( 'length' ) )
            // InternalMiniJava.g:6459:1: ( 'length' )
            {
            // InternalMiniJava.g:6459:1: ( 'length' )
            // InternalMiniJava.g:6460:2: 'length'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getArrayLengthAccess().getLengthKeyword_1_2()); 
            }
            match(input,57,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getArrayLengthAccess().getLengthKeyword_1_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayLength__Group_1__2__Impl"


    // $ANTLR start "rule__Primary__Group_0__0"
    // InternalMiniJava.g:6470:1: rule__Primary__Group_0__0 : rule__Primary__Group_0__0__Impl rule__Primary__Group_0__1 ;
    public final void rule__Primary__Group_0__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6474:1: ( rule__Primary__Group_0__0__Impl rule__Primary__Group_0__1 )
            // InternalMiniJava.g:6475:2: rule__Primary__Group_0__0__Impl rule__Primary__Group_0__1
            {
            pushFollow(FOLLOW_25);
            rule__Primary__Group_0__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Primary__Group_0__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Primary__Group_0__0"


    // $ANTLR start "rule__Primary__Group_0__0__Impl"
    // InternalMiniJava.g:6482:1: rule__Primary__Group_0__0__Impl : ( '(' ) ;
    public final void rule__Primary__Group_0__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6486:1: ( ( '(' ) )
            // InternalMiniJava.g:6487:1: ( '(' )
            {
            // InternalMiniJava.g:6487:1: ( '(' )
            // InternalMiniJava.g:6488:2: '('
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrimaryAccess().getLeftParenthesisKeyword_0_0()); 
            }
            match(input,28,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrimaryAccess().getLeftParenthesisKeyword_0_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Primary__Group_0__0__Impl"


    // $ANTLR start "rule__Primary__Group_0__1"
    // InternalMiniJava.g:6497:1: rule__Primary__Group_0__1 : rule__Primary__Group_0__1__Impl rule__Primary__Group_0__2 ;
    public final void rule__Primary__Group_0__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6501:1: ( rule__Primary__Group_0__1__Impl rule__Primary__Group_0__2 )
            // InternalMiniJava.g:6502:2: rule__Primary__Group_0__1__Impl rule__Primary__Group_0__2
            {
            pushFollow(FOLLOW_32);
            rule__Primary__Group_0__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Primary__Group_0__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Primary__Group_0__1"


    // $ANTLR start "rule__Primary__Group_0__1__Impl"
    // InternalMiniJava.g:6509:1: rule__Primary__Group_0__1__Impl : ( ruleExpression ) ;
    public final void rule__Primary__Group_0__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6513:1: ( ( ruleExpression ) )
            // InternalMiniJava.g:6514:1: ( ruleExpression )
            {
            // InternalMiniJava.g:6514:1: ( ruleExpression )
            // InternalMiniJava.g:6515:2: ruleExpression
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrimaryAccess().getExpressionParserRuleCall_0_1()); 
            }
            pushFollow(FOLLOW_2);
            ruleExpression();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrimaryAccess().getExpressionParserRuleCall_0_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Primary__Group_0__1__Impl"


    // $ANTLR start "rule__Primary__Group_0__2"
    // InternalMiniJava.g:6524:1: rule__Primary__Group_0__2 : rule__Primary__Group_0__2__Impl ;
    public final void rule__Primary__Group_0__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6528:1: ( rule__Primary__Group_0__2__Impl )
            // InternalMiniJava.g:6529:2: rule__Primary__Group_0__2__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Primary__Group_0__2__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Primary__Group_0__2"


    // $ANTLR start "rule__Primary__Group_0__2__Impl"
    // InternalMiniJava.g:6535:1: rule__Primary__Group_0__2__Impl : ( ')' ) ;
    public final void rule__Primary__Group_0__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6539:1: ( ( ')' ) )
            // InternalMiniJava.g:6540:1: ( ')' )
            {
            // InternalMiniJava.g:6540:1: ( ')' )
            // InternalMiniJava.g:6541:2: ')'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrimaryAccess().getRightParenthesisKeyword_0_2()); 
            }
            match(input,29,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrimaryAccess().getRightParenthesisKeyword_0_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Primary__Group_0__2__Impl"


    // $ANTLR start "rule__Primary__Group_1__0"
    // InternalMiniJava.g:6551:1: rule__Primary__Group_1__0 : rule__Primary__Group_1__0__Impl rule__Primary__Group_1__1 ;
    public final void rule__Primary__Group_1__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6555:1: ( rule__Primary__Group_1__0__Impl rule__Primary__Group_1__1 )
            // InternalMiniJava.g:6556:2: rule__Primary__Group_1__0__Impl rule__Primary__Group_1__1
            {
            pushFollow(FOLLOW_60);
            rule__Primary__Group_1__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Primary__Group_1__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Primary__Group_1__0"


    // $ANTLR start "rule__Primary__Group_1__0__Impl"
    // InternalMiniJava.g:6563:1: rule__Primary__Group_1__0__Impl : ( () ) ;
    public final void rule__Primary__Group_1__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6567:1: ( ( () ) )
            // InternalMiniJava.g:6568:1: ( () )
            {
            // InternalMiniJava.g:6568:1: ( () )
            // InternalMiniJava.g:6569:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrimaryAccess().getNotAction_1_0()); 
            }
            // InternalMiniJava.g:6570:2: ()
            // InternalMiniJava.g:6570:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrimaryAccess().getNotAction_1_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Primary__Group_1__0__Impl"


    // $ANTLR start "rule__Primary__Group_1__1"
    // InternalMiniJava.g:6578:1: rule__Primary__Group_1__1 : rule__Primary__Group_1__1__Impl rule__Primary__Group_1__2 ;
    public final void rule__Primary__Group_1__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6582:1: ( rule__Primary__Group_1__1__Impl rule__Primary__Group_1__2 )
            // InternalMiniJava.g:6583:2: rule__Primary__Group_1__1__Impl rule__Primary__Group_1__2
            {
            pushFollow(FOLLOW_25);
            rule__Primary__Group_1__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Primary__Group_1__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Primary__Group_1__1"


    // $ANTLR start "rule__Primary__Group_1__1__Impl"
    // InternalMiniJava.g:6590:1: rule__Primary__Group_1__1__Impl : ( ( '!' ) ) ;
    public final void rule__Primary__Group_1__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6594:1: ( ( ( '!' ) ) )
            // InternalMiniJava.g:6595:1: ( ( '!' ) )
            {
            // InternalMiniJava.g:6595:1: ( ( '!' ) )
            // InternalMiniJava.g:6596:2: ( '!' )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrimaryAccess().getExclamationMarkKeyword_1_1()); 
            }
            // InternalMiniJava.g:6597:2: ( '!' )
            // InternalMiniJava.g:6597:3: '!'
            {
            match(input,58,FOLLOW_2); if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrimaryAccess().getExclamationMarkKeyword_1_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Primary__Group_1__1__Impl"


    // $ANTLR start "rule__Primary__Group_1__2"
    // InternalMiniJava.g:6605:1: rule__Primary__Group_1__2 : rule__Primary__Group_1__2__Impl ;
    public final void rule__Primary__Group_1__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6609:1: ( rule__Primary__Group_1__2__Impl )
            // InternalMiniJava.g:6610:2: rule__Primary__Group_1__2__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Primary__Group_1__2__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Primary__Group_1__2"


    // $ANTLR start "rule__Primary__Group_1__2__Impl"
    // InternalMiniJava.g:6616:1: rule__Primary__Group_1__2__Impl : ( ( rule__Primary__ExpressionAssignment_1_2 ) ) ;
    public final void rule__Primary__Group_1__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6620:1: ( ( ( rule__Primary__ExpressionAssignment_1_2 ) ) )
            // InternalMiniJava.g:6621:1: ( ( rule__Primary__ExpressionAssignment_1_2 ) )
            {
            // InternalMiniJava.g:6621:1: ( ( rule__Primary__ExpressionAssignment_1_2 ) )
            // InternalMiniJava.g:6622:2: ( rule__Primary__ExpressionAssignment_1_2 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrimaryAccess().getExpressionAssignment_1_2()); 
            }
            // InternalMiniJava.g:6623:2: ( rule__Primary__ExpressionAssignment_1_2 )
            // InternalMiniJava.g:6623:3: rule__Primary__ExpressionAssignment_1_2
            {
            pushFollow(FOLLOW_2);
            rule__Primary__ExpressionAssignment_1_2();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrimaryAccess().getExpressionAssignment_1_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Primary__Group_1__2__Impl"


    // $ANTLR start "rule__Primary__Group_2__0"
    // InternalMiniJava.g:6632:1: rule__Primary__Group_2__0 : rule__Primary__Group_2__0__Impl rule__Primary__Group_2__1 ;
    public final void rule__Primary__Group_2__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6636:1: ( rule__Primary__Group_2__0__Impl rule__Primary__Group_2__1 )
            // InternalMiniJava.g:6637:2: rule__Primary__Group_2__0__Impl rule__Primary__Group_2__1
            {
            pushFollow(FOLLOW_61);
            rule__Primary__Group_2__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Primary__Group_2__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Primary__Group_2__0"


    // $ANTLR start "rule__Primary__Group_2__0__Impl"
    // InternalMiniJava.g:6644:1: rule__Primary__Group_2__0__Impl : ( () ) ;
    public final void rule__Primary__Group_2__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6648:1: ( ( () ) )
            // InternalMiniJava.g:6649:1: ( () )
            {
            // InternalMiniJava.g:6649:1: ( () )
            // InternalMiniJava.g:6650:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrimaryAccess().getNegAction_2_0()); 
            }
            // InternalMiniJava.g:6651:2: ()
            // InternalMiniJava.g:6651:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrimaryAccess().getNegAction_2_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Primary__Group_2__0__Impl"


    // $ANTLR start "rule__Primary__Group_2__1"
    // InternalMiniJava.g:6659:1: rule__Primary__Group_2__1 : rule__Primary__Group_2__1__Impl rule__Primary__Group_2__2 ;
    public final void rule__Primary__Group_2__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6663:1: ( rule__Primary__Group_2__1__Impl rule__Primary__Group_2__2 )
            // InternalMiniJava.g:6664:2: rule__Primary__Group_2__1__Impl rule__Primary__Group_2__2
            {
            pushFollow(FOLLOW_25);
            rule__Primary__Group_2__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__Primary__Group_2__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Primary__Group_2__1"


    // $ANTLR start "rule__Primary__Group_2__1__Impl"
    // InternalMiniJava.g:6671:1: rule__Primary__Group_2__1__Impl : ( ( '-' ) ) ;
    public final void rule__Primary__Group_2__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6675:1: ( ( ( '-' ) ) )
            // InternalMiniJava.g:6676:1: ( ( '-' ) )
            {
            // InternalMiniJava.g:6676:1: ( ( '-' ) )
            // InternalMiniJava.g:6677:2: ( '-' )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrimaryAccess().getHyphenMinusKeyword_2_1()); 
            }
            // InternalMiniJava.g:6678:2: ( '-' )
            // InternalMiniJava.g:6678:3: '-'
            {
            match(input,54,FOLLOW_2); if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrimaryAccess().getHyphenMinusKeyword_2_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Primary__Group_2__1__Impl"


    // $ANTLR start "rule__Primary__Group_2__2"
    // InternalMiniJava.g:6686:1: rule__Primary__Group_2__2 : rule__Primary__Group_2__2__Impl ;
    public final void rule__Primary__Group_2__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6690:1: ( rule__Primary__Group_2__2__Impl )
            // InternalMiniJava.g:6691:2: rule__Primary__Group_2__2__Impl
            {
            pushFollow(FOLLOW_2);
            rule__Primary__Group_2__2__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Primary__Group_2__2"


    // $ANTLR start "rule__Primary__Group_2__2__Impl"
    // InternalMiniJava.g:6697:1: rule__Primary__Group_2__2__Impl : ( ( rule__Primary__ExpressionAssignment_2_2 ) ) ;
    public final void rule__Primary__Group_2__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6701:1: ( ( ( rule__Primary__ExpressionAssignment_2_2 ) ) )
            // InternalMiniJava.g:6702:1: ( ( rule__Primary__ExpressionAssignment_2_2 ) )
            {
            // InternalMiniJava.g:6702:1: ( ( rule__Primary__ExpressionAssignment_2_2 ) )
            // InternalMiniJava.g:6703:2: ( rule__Primary__ExpressionAssignment_2_2 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrimaryAccess().getExpressionAssignment_2_2()); 
            }
            // InternalMiniJava.g:6704:2: ( rule__Primary__ExpressionAssignment_2_2 )
            // InternalMiniJava.g:6704:3: rule__Primary__ExpressionAssignment_2_2
            {
            pushFollow(FOLLOW_2);
            rule__Primary__ExpressionAssignment_2_2();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrimaryAccess().getExpressionAssignment_2_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Primary__Group_2__2__Impl"


    // $ANTLR start "rule__SelectionExpression__Group__0"
    // InternalMiniJava.g:6713:1: rule__SelectionExpression__Group__0 : rule__SelectionExpression__Group__0__Impl rule__SelectionExpression__Group__1 ;
    public final void rule__SelectionExpression__Group__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6717:1: ( rule__SelectionExpression__Group__0__Impl rule__SelectionExpression__Group__1 )
            // InternalMiniJava.g:6718:2: rule__SelectionExpression__Group__0__Impl rule__SelectionExpression__Group__1
            {
            pushFollow(FOLLOW_8);
            rule__SelectionExpression__Group__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__SelectionExpression__Group__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group__0"


    // $ANTLR start "rule__SelectionExpression__Group__0__Impl"
    // InternalMiniJava.g:6725:1: rule__SelectionExpression__Group__0__Impl : ( ruleTerminalExpression ) ;
    public final void rule__SelectionExpression__Group__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6729:1: ( ( ruleTerminalExpression ) )
            // InternalMiniJava.g:6730:1: ( ruleTerminalExpression )
            {
            // InternalMiniJava.g:6730:1: ( ruleTerminalExpression )
            // InternalMiniJava.g:6731:2: ruleTerminalExpression
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionAccess().getTerminalExpressionParserRuleCall_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleTerminalExpression();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionAccess().getTerminalExpressionParserRuleCall_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group__0__Impl"


    // $ANTLR start "rule__SelectionExpression__Group__1"
    // InternalMiniJava.g:6740:1: rule__SelectionExpression__Group__1 : rule__SelectionExpression__Group__1__Impl ;
    public final void rule__SelectionExpression__Group__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6744:1: ( rule__SelectionExpression__Group__1__Impl )
            // InternalMiniJava.g:6745:2: rule__SelectionExpression__Group__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__SelectionExpression__Group__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group__1"


    // $ANTLR start "rule__SelectionExpression__Group__1__Impl"
    // InternalMiniJava.g:6751:1: rule__SelectionExpression__Group__1__Impl : ( ( rule__SelectionExpression__Alternatives_1 )* ) ;
    public final void rule__SelectionExpression__Group__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6755:1: ( ( ( rule__SelectionExpression__Alternatives_1 )* ) )
            // InternalMiniJava.g:6756:1: ( ( rule__SelectionExpression__Alternatives_1 )* )
            {
            // InternalMiniJava.g:6756:1: ( ( rule__SelectionExpression__Alternatives_1 )* )
            // InternalMiniJava.g:6757:2: ( rule__SelectionExpression__Alternatives_1 )*
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionAccess().getAlternatives_1()); 
            }
            // InternalMiniJava.g:6758:2: ( rule__SelectionExpression__Alternatives_1 )*
            loop52:
            do {
                int alt52=2;
                int LA52_0 = input.LA(1);

                if ( (LA52_0==19) ) {
                    int LA52_2 = input.LA(2);

                    if ( (LA52_2==RULE_ID) ) {
                        alt52=1;
                    }


                }


                switch (alt52) {
            	case 1 :
            	    // InternalMiniJava.g:6758:3: rule__SelectionExpression__Alternatives_1
            	    {
            	    pushFollow(FOLLOW_9);
            	    rule__SelectionExpression__Alternatives_1();

            	    state._fsp--;
            	    if (state.failed) return ;

            	    }
            	    break;

            	default :
            	    break loop52;
                }
            } while (true);

            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionAccess().getAlternatives_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group__1__Impl"


    // $ANTLR start "rule__SelectionExpression__Group_1_0__0"
    // InternalMiniJava.g:6767:1: rule__SelectionExpression__Group_1_0__0 : rule__SelectionExpression__Group_1_0__0__Impl rule__SelectionExpression__Group_1_0__1 ;
    public final void rule__SelectionExpression__Group_1_0__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6771:1: ( rule__SelectionExpression__Group_1_0__0__Impl rule__SelectionExpression__Group_1_0__1 )
            // InternalMiniJava.g:6772:2: rule__SelectionExpression__Group_1_0__0__Impl rule__SelectionExpression__Group_1_0__1
            {
            pushFollow(FOLLOW_8);
            rule__SelectionExpression__Group_1_0__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__SelectionExpression__Group_1_0__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_0__0"


    // $ANTLR start "rule__SelectionExpression__Group_1_0__0__Impl"
    // InternalMiniJava.g:6779:1: rule__SelectionExpression__Group_1_0__0__Impl : ( () ) ;
    public final void rule__SelectionExpression__Group_1_0__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6783:1: ( ( () ) )
            // InternalMiniJava.g:6784:1: ( () )
            {
            // InternalMiniJava.g:6784:1: ( () )
            // InternalMiniJava.g:6785:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionAccess().getFieldAccessReceiverAction_1_0_0()); 
            }
            // InternalMiniJava.g:6786:2: ()
            // InternalMiniJava.g:6786:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionAccess().getFieldAccessReceiverAction_1_0_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_0__0__Impl"


    // $ANTLR start "rule__SelectionExpression__Group_1_0__1"
    // InternalMiniJava.g:6794:1: rule__SelectionExpression__Group_1_0__1 : rule__SelectionExpression__Group_1_0__1__Impl rule__SelectionExpression__Group_1_0__2 ;
    public final void rule__SelectionExpression__Group_1_0__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6798:1: ( rule__SelectionExpression__Group_1_0__1__Impl rule__SelectionExpression__Group_1_0__2 )
            // InternalMiniJava.g:6799:2: rule__SelectionExpression__Group_1_0__1__Impl rule__SelectionExpression__Group_1_0__2
            {
            pushFollow(FOLLOW_6);
            rule__SelectionExpression__Group_1_0__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__SelectionExpression__Group_1_0__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_0__1"


    // $ANTLR start "rule__SelectionExpression__Group_1_0__1__Impl"
    // InternalMiniJava.g:6806:1: rule__SelectionExpression__Group_1_0__1__Impl : ( '.' ) ;
    public final void rule__SelectionExpression__Group_1_0__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6810:1: ( ( '.' ) )
            // InternalMiniJava.g:6811:1: ( '.' )
            {
            // InternalMiniJava.g:6811:1: ( '.' )
            // InternalMiniJava.g:6812:2: '.'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionAccess().getFullStopKeyword_1_0_1()); 
            }
            match(input,19,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionAccess().getFullStopKeyword_1_0_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_0__1__Impl"


    // $ANTLR start "rule__SelectionExpression__Group_1_0__2"
    // InternalMiniJava.g:6821:1: rule__SelectionExpression__Group_1_0__2 : rule__SelectionExpression__Group_1_0__2__Impl ;
    public final void rule__SelectionExpression__Group_1_0__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6825:1: ( rule__SelectionExpression__Group_1_0__2__Impl )
            // InternalMiniJava.g:6826:2: rule__SelectionExpression__Group_1_0__2__Impl
            {
            pushFollow(FOLLOW_2);
            rule__SelectionExpression__Group_1_0__2__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_0__2"


    // $ANTLR start "rule__SelectionExpression__Group_1_0__2__Impl"
    // InternalMiniJava.g:6832:1: rule__SelectionExpression__Group_1_0__2__Impl : ( ( rule__SelectionExpression__FieldAssignment_1_0_2 ) ) ;
    public final void rule__SelectionExpression__Group_1_0__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6836:1: ( ( ( rule__SelectionExpression__FieldAssignment_1_0_2 ) ) )
            // InternalMiniJava.g:6837:1: ( ( rule__SelectionExpression__FieldAssignment_1_0_2 ) )
            {
            // InternalMiniJava.g:6837:1: ( ( rule__SelectionExpression__FieldAssignment_1_0_2 ) )
            // InternalMiniJava.g:6838:2: ( rule__SelectionExpression__FieldAssignment_1_0_2 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionAccess().getFieldAssignment_1_0_2()); 
            }
            // InternalMiniJava.g:6839:2: ( rule__SelectionExpression__FieldAssignment_1_0_2 )
            // InternalMiniJava.g:6839:3: rule__SelectionExpression__FieldAssignment_1_0_2
            {
            pushFollow(FOLLOW_2);
            rule__SelectionExpression__FieldAssignment_1_0_2();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionAccess().getFieldAssignment_1_0_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_0__2__Impl"


    // $ANTLR start "rule__SelectionExpression__Group_1_1__0"
    // InternalMiniJava.g:6848:1: rule__SelectionExpression__Group_1_1__0 : rule__SelectionExpression__Group_1_1__0__Impl rule__SelectionExpression__Group_1_1__1 ;
    public final void rule__SelectionExpression__Group_1_1__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6852:1: ( rule__SelectionExpression__Group_1_1__0__Impl rule__SelectionExpression__Group_1_1__1 )
            // InternalMiniJava.g:6853:2: rule__SelectionExpression__Group_1_1__0__Impl rule__SelectionExpression__Group_1_1__1
            {
            pushFollow(FOLLOW_8);
            rule__SelectionExpression__Group_1_1__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__SelectionExpression__Group_1_1__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_1__0"


    // $ANTLR start "rule__SelectionExpression__Group_1_1__0__Impl"
    // InternalMiniJava.g:6860:1: rule__SelectionExpression__Group_1_1__0__Impl : ( () ) ;
    public final void rule__SelectionExpression__Group_1_1__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6864:1: ( ( () ) )
            // InternalMiniJava.g:6865:1: ( () )
            {
            // InternalMiniJava.g:6865:1: ( () )
            // InternalMiniJava.g:6866:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionAccess().getMethodCallReceiverAction_1_1_0()); 
            }
            // InternalMiniJava.g:6867:2: ()
            // InternalMiniJava.g:6867:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionAccess().getMethodCallReceiverAction_1_1_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_1__0__Impl"


    // $ANTLR start "rule__SelectionExpression__Group_1_1__1"
    // InternalMiniJava.g:6875:1: rule__SelectionExpression__Group_1_1__1 : rule__SelectionExpression__Group_1_1__1__Impl rule__SelectionExpression__Group_1_1__2 ;
    public final void rule__SelectionExpression__Group_1_1__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6879:1: ( rule__SelectionExpression__Group_1_1__1__Impl rule__SelectionExpression__Group_1_1__2 )
            // InternalMiniJava.g:6880:2: rule__SelectionExpression__Group_1_1__1__Impl rule__SelectionExpression__Group_1_1__2
            {
            pushFollow(FOLLOW_6);
            rule__SelectionExpression__Group_1_1__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__SelectionExpression__Group_1_1__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_1__1"


    // $ANTLR start "rule__SelectionExpression__Group_1_1__1__Impl"
    // InternalMiniJava.g:6887:1: rule__SelectionExpression__Group_1_1__1__Impl : ( '.' ) ;
    public final void rule__SelectionExpression__Group_1_1__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6891:1: ( ( '.' ) )
            // InternalMiniJava.g:6892:1: ( '.' )
            {
            // InternalMiniJava.g:6892:1: ( '.' )
            // InternalMiniJava.g:6893:2: '.'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionAccess().getFullStopKeyword_1_1_1()); 
            }
            match(input,19,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionAccess().getFullStopKeyword_1_1_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_1__1__Impl"


    // $ANTLR start "rule__SelectionExpression__Group_1_1__2"
    // InternalMiniJava.g:6902:1: rule__SelectionExpression__Group_1_1__2 : rule__SelectionExpression__Group_1_1__2__Impl rule__SelectionExpression__Group_1_1__3 ;
    public final void rule__SelectionExpression__Group_1_1__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6906:1: ( rule__SelectionExpression__Group_1_1__2__Impl rule__SelectionExpression__Group_1_1__3 )
            // InternalMiniJava.g:6907:2: rule__SelectionExpression__Group_1_1__2__Impl rule__SelectionExpression__Group_1_1__3
            {
            pushFollow(FOLLOW_31);
            rule__SelectionExpression__Group_1_1__2__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__SelectionExpression__Group_1_1__3();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_1__2"


    // $ANTLR start "rule__SelectionExpression__Group_1_1__2__Impl"
    // InternalMiniJava.g:6914:1: rule__SelectionExpression__Group_1_1__2__Impl : ( ( rule__SelectionExpression__MethodAssignment_1_1_2 ) ) ;
    public final void rule__SelectionExpression__Group_1_1__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6918:1: ( ( ( rule__SelectionExpression__MethodAssignment_1_1_2 ) ) )
            // InternalMiniJava.g:6919:1: ( ( rule__SelectionExpression__MethodAssignment_1_1_2 ) )
            {
            // InternalMiniJava.g:6919:1: ( ( rule__SelectionExpression__MethodAssignment_1_1_2 ) )
            // InternalMiniJava.g:6920:2: ( rule__SelectionExpression__MethodAssignment_1_1_2 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionAccess().getMethodAssignment_1_1_2()); 
            }
            // InternalMiniJava.g:6921:2: ( rule__SelectionExpression__MethodAssignment_1_1_2 )
            // InternalMiniJava.g:6921:3: rule__SelectionExpression__MethodAssignment_1_1_2
            {
            pushFollow(FOLLOW_2);
            rule__SelectionExpression__MethodAssignment_1_1_2();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionAccess().getMethodAssignment_1_1_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_1__2__Impl"


    // $ANTLR start "rule__SelectionExpression__Group_1_1__3"
    // InternalMiniJava.g:6929:1: rule__SelectionExpression__Group_1_1__3 : rule__SelectionExpression__Group_1_1__3__Impl rule__SelectionExpression__Group_1_1__4 ;
    public final void rule__SelectionExpression__Group_1_1__3() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6933:1: ( rule__SelectionExpression__Group_1_1__3__Impl rule__SelectionExpression__Group_1_1__4 )
            // InternalMiniJava.g:6934:2: rule__SelectionExpression__Group_1_1__3__Impl rule__SelectionExpression__Group_1_1__4
            {
            pushFollow(FOLLOW_62);
            rule__SelectionExpression__Group_1_1__3__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__SelectionExpression__Group_1_1__4();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_1__3"


    // $ANTLR start "rule__SelectionExpression__Group_1_1__3__Impl"
    // InternalMiniJava.g:6941:1: rule__SelectionExpression__Group_1_1__3__Impl : ( '(' ) ;
    public final void rule__SelectionExpression__Group_1_1__3__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6945:1: ( ( '(' ) )
            // InternalMiniJava.g:6946:1: ( '(' )
            {
            // InternalMiniJava.g:6946:1: ( '(' )
            // InternalMiniJava.g:6947:2: '('
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionAccess().getLeftParenthesisKeyword_1_1_3()); 
            }
            match(input,28,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionAccess().getLeftParenthesisKeyword_1_1_3()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_1__3__Impl"


    // $ANTLR start "rule__SelectionExpression__Group_1_1__4"
    // InternalMiniJava.g:6956:1: rule__SelectionExpression__Group_1_1__4 : rule__SelectionExpression__Group_1_1__4__Impl rule__SelectionExpression__Group_1_1__5 ;
    public final void rule__SelectionExpression__Group_1_1__4() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6960:1: ( rule__SelectionExpression__Group_1_1__4__Impl rule__SelectionExpression__Group_1_1__5 )
            // InternalMiniJava.g:6961:2: rule__SelectionExpression__Group_1_1__4__Impl rule__SelectionExpression__Group_1_1__5
            {
            pushFollow(FOLLOW_62);
            rule__SelectionExpression__Group_1_1__4__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__SelectionExpression__Group_1_1__5();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_1__4"


    // $ANTLR start "rule__SelectionExpression__Group_1_1__4__Impl"
    // InternalMiniJava.g:6968:1: rule__SelectionExpression__Group_1_1__4__Impl : ( ( rule__SelectionExpression__Group_1_1_4__0 )? ) ;
    public final void rule__SelectionExpression__Group_1_1__4__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6972:1: ( ( ( rule__SelectionExpression__Group_1_1_4__0 )? ) )
            // InternalMiniJava.g:6973:1: ( ( rule__SelectionExpression__Group_1_1_4__0 )? )
            {
            // InternalMiniJava.g:6973:1: ( ( rule__SelectionExpression__Group_1_1_4__0 )? )
            // InternalMiniJava.g:6974:2: ( rule__SelectionExpression__Group_1_1_4__0 )?
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionAccess().getGroup_1_1_4()); 
            }
            // InternalMiniJava.g:6975:2: ( rule__SelectionExpression__Group_1_1_4__0 )?
            int alt53=2;
            int LA53_0 = input.LA(1);

            if ( ((LA53_0>=RULE_ID && LA53_0<=RULE_INT)||(LA53_0>=12 && LA53_0<=13)||LA53_0==28||LA53_0==54||(LA53_0>=58 && LA53_0<=62)) ) {
                alt53=1;
            }
            switch (alt53) {
                case 1 :
                    // InternalMiniJava.g:6975:3: rule__SelectionExpression__Group_1_1_4__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__SelectionExpression__Group_1_1_4__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionAccess().getGroup_1_1_4()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_1__4__Impl"


    // $ANTLR start "rule__SelectionExpression__Group_1_1__5"
    // InternalMiniJava.g:6983:1: rule__SelectionExpression__Group_1_1__5 : rule__SelectionExpression__Group_1_1__5__Impl ;
    public final void rule__SelectionExpression__Group_1_1__5() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6987:1: ( rule__SelectionExpression__Group_1_1__5__Impl )
            // InternalMiniJava.g:6988:2: rule__SelectionExpression__Group_1_1__5__Impl
            {
            pushFollow(FOLLOW_2);
            rule__SelectionExpression__Group_1_1__5__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_1__5"


    // $ANTLR start "rule__SelectionExpression__Group_1_1__5__Impl"
    // InternalMiniJava.g:6994:1: rule__SelectionExpression__Group_1_1__5__Impl : ( ')' ) ;
    public final void rule__SelectionExpression__Group_1_1__5__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:6998:1: ( ( ')' ) )
            // InternalMiniJava.g:6999:1: ( ')' )
            {
            // InternalMiniJava.g:6999:1: ( ')' )
            // InternalMiniJava.g:7000:2: ')'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionAccess().getRightParenthesisKeyword_1_1_5()); 
            }
            match(input,29,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionAccess().getRightParenthesisKeyword_1_1_5()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_1__5__Impl"


    // $ANTLR start "rule__SelectionExpression__Group_1_1_4__0"
    // InternalMiniJava.g:7010:1: rule__SelectionExpression__Group_1_1_4__0 : rule__SelectionExpression__Group_1_1_4__0__Impl rule__SelectionExpression__Group_1_1_4__1 ;
    public final void rule__SelectionExpression__Group_1_1_4__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7014:1: ( rule__SelectionExpression__Group_1_1_4__0__Impl rule__SelectionExpression__Group_1_1_4__1 )
            // InternalMiniJava.g:7015:2: rule__SelectionExpression__Group_1_1_4__0__Impl rule__SelectionExpression__Group_1_1_4__1
            {
            pushFollow(FOLLOW_15);
            rule__SelectionExpression__Group_1_1_4__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__SelectionExpression__Group_1_1_4__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_1_4__0"


    // $ANTLR start "rule__SelectionExpression__Group_1_1_4__0__Impl"
    // InternalMiniJava.g:7022:1: rule__SelectionExpression__Group_1_1_4__0__Impl : ( ( rule__SelectionExpression__ArgsAssignment_1_1_4_0 ) ) ;
    public final void rule__SelectionExpression__Group_1_1_4__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7026:1: ( ( ( rule__SelectionExpression__ArgsAssignment_1_1_4_0 ) ) )
            // InternalMiniJava.g:7027:1: ( ( rule__SelectionExpression__ArgsAssignment_1_1_4_0 ) )
            {
            // InternalMiniJava.g:7027:1: ( ( rule__SelectionExpression__ArgsAssignment_1_1_4_0 ) )
            // InternalMiniJava.g:7028:2: ( rule__SelectionExpression__ArgsAssignment_1_1_4_0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionAccess().getArgsAssignment_1_1_4_0()); 
            }
            // InternalMiniJava.g:7029:2: ( rule__SelectionExpression__ArgsAssignment_1_1_4_0 )
            // InternalMiniJava.g:7029:3: rule__SelectionExpression__ArgsAssignment_1_1_4_0
            {
            pushFollow(FOLLOW_2);
            rule__SelectionExpression__ArgsAssignment_1_1_4_0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionAccess().getArgsAssignment_1_1_4_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_1_4__0__Impl"


    // $ANTLR start "rule__SelectionExpression__Group_1_1_4__1"
    // InternalMiniJava.g:7037:1: rule__SelectionExpression__Group_1_1_4__1 : rule__SelectionExpression__Group_1_1_4__1__Impl ;
    public final void rule__SelectionExpression__Group_1_1_4__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7041:1: ( rule__SelectionExpression__Group_1_1_4__1__Impl )
            // InternalMiniJava.g:7042:2: rule__SelectionExpression__Group_1_1_4__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__SelectionExpression__Group_1_1_4__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_1_4__1"


    // $ANTLR start "rule__SelectionExpression__Group_1_1_4__1__Impl"
    // InternalMiniJava.g:7048:1: rule__SelectionExpression__Group_1_1_4__1__Impl : ( ( rule__SelectionExpression__Group_1_1_4_1__0 )* ) ;
    public final void rule__SelectionExpression__Group_1_1_4__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7052:1: ( ( ( rule__SelectionExpression__Group_1_1_4_1__0 )* ) )
            // InternalMiniJava.g:7053:1: ( ( rule__SelectionExpression__Group_1_1_4_1__0 )* )
            {
            // InternalMiniJava.g:7053:1: ( ( rule__SelectionExpression__Group_1_1_4_1__0 )* )
            // InternalMiniJava.g:7054:2: ( rule__SelectionExpression__Group_1_1_4_1__0 )*
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionAccess().getGroup_1_1_4_1()); 
            }
            // InternalMiniJava.g:7055:2: ( rule__SelectionExpression__Group_1_1_4_1__0 )*
            loop54:
            do {
                int alt54=2;
                int LA54_0 = input.LA(1);

                if ( (LA54_0==26) ) {
                    alt54=1;
                }


                switch (alt54) {
            	case 1 :
            	    // InternalMiniJava.g:7055:3: rule__SelectionExpression__Group_1_1_4_1__0
            	    {
            	    pushFollow(FOLLOW_16);
            	    rule__SelectionExpression__Group_1_1_4_1__0();

            	    state._fsp--;
            	    if (state.failed) return ;

            	    }
            	    break;

            	default :
            	    break loop54;
                }
            } while (true);

            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionAccess().getGroup_1_1_4_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_1_4__1__Impl"


    // $ANTLR start "rule__SelectionExpression__Group_1_1_4_1__0"
    // InternalMiniJava.g:7064:1: rule__SelectionExpression__Group_1_1_4_1__0 : rule__SelectionExpression__Group_1_1_4_1__0__Impl rule__SelectionExpression__Group_1_1_4_1__1 ;
    public final void rule__SelectionExpression__Group_1_1_4_1__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7068:1: ( rule__SelectionExpression__Group_1_1_4_1__0__Impl rule__SelectionExpression__Group_1_1_4_1__1 )
            // InternalMiniJava.g:7069:2: rule__SelectionExpression__Group_1_1_4_1__0__Impl rule__SelectionExpression__Group_1_1_4_1__1
            {
            pushFollow(FOLLOW_25);
            rule__SelectionExpression__Group_1_1_4_1__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__SelectionExpression__Group_1_1_4_1__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_1_4_1__0"


    // $ANTLR start "rule__SelectionExpression__Group_1_1_4_1__0__Impl"
    // InternalMiniJava.g:7076:1: rule__SelectionExpression__Group_1_1_4_1__0__Impl : ( ',' ) ;
    public final void rule__SelectionExpression__Group_1_1_4_1__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7080:1: ( ( ',' ) )
            // InternalMiniJava.g:7081:1: ( ',' )
            {
            // InternalMiniJava.g:7081:1: ( ',' )
            // InternalMiniJava.g:7082:2: ','
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionAccess().getCommaKeyword_1_1_4_1_0()); 
            }
            match(input,26,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionAccess().getCommaKeyword_1_1_4_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_1_4_1__0__Impl"


    // $ANTLR start "rule__SelectionExpression__Group_1_1_4_1__1"
    // InternalMiniJava.g:7091:1: rule__SelectionExpression__Group_1_1_4_1__1 : rule__SelectionExpression__Group_1_1_4_1__1__Impl ;
    public final void rule__SelectionExpression__Group_1_1_4_1__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7095:1: ( rule__SelectionExpression__Group_1_1_4_1__1__Impl )
            // InternalMiniJava.g:7096:2: rule__SelectionExpression__Group_1_1_4_1__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__SelectionExpression__Group_1_1_4_1__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_1_4_1__1"


    // $ANTLR start "rule__SelectionExpression__Group_1_1_4_1__1__Impl"
    // InternalMiniJava.g:7102:1: rule__SelectionExpression__Group_1_1_4_1__1__Impl : ( ( rule__SelectionExpression__ArgsAssignment_1_1_4_1_1 ) ) ;
    public final void rule__SelectionExpression__Group_1_1_4_1__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7106:1: ( ( ( rule__SelectionExpression__ArgsAssignment_1_1_4_1_1 ) ) )
            // InternalMiniJava.g:7107:1: ( ( rule__SelectionExpression__ArgsAssignment_1_1_4_1_1 ) )
            {
            // InternalMiniJava.g:7107:1: ( ( rule__SelectionExpression__ArgsAssignment_1_1_4_1_1 ) )
            // InternalMiniJava.g:7108:2: ( rule__SelectionExpression__ArgsAssignment_1_1_4_1_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionAccess().getArgsAssignment_1_1_4_1_1()); 
            }
            // InternalMiniJava.g:7109:2: ( rule__SelectionExpression__ArgsAssignment_1_1_4_1_1 )
            // InternalMiniJava.g:7109:3: rule__SelectionExpression__ArgsAssignment_1_1_4_1_1
            {
            pushFollow(FOLLOW_2);
            rule__SelectionExpression__ArgsAssignment_1_1_4_1_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionAccess().getArgsAssignment_1_1_4_1_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__Group_1_1_4_1__1__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_0__0"
    // InternalMiniJava.g:7118:1: rule__TerminalExpression__Group_0__0 : rule__TerminalExpression__Group_0__0__Impl rule__TerminalExpression__Group_0__1 ;
    public final void rule__TerminalExpression__Group_0__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7122:1: ( rule__TerminalExpression__Group_0__0__Impl rule__TerminalExpression__Group_0__1 )
            // InternalMiniJava.g:7123:2: rule__TerminalExpression__Group_0__0__Impl rule__TerminalExpression__Group_0__1
            {
            pushFollow(FOLLOW_63);
            rule__TerminalExpression__Group_0__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_0__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_0__0"


    // $ANTLR start "rule__TerminalExpression__Group_0__0__Impl"
    // InternalMiniJava.g:7130:1: rule__TerminalExpression__Group_0__0__Impl : ( () ) ;
    public final void rule__TerminalExpression__Group_0__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7134:1: ( ( () ) )
            // InternalMiniJava.g:7135:1: ( () )
            {
            // InternalMiniJava.g:7135:1: ( () )
            // InternalMiniJava.g:7136:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getStringConstantAction_0_0()); 
            }
            // InternalMiniJava.g:7137:2: ()
            // InternalMiniJava.g:7137:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getStringConstantAction_0_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_0__0__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_0__1"
    // InternalMiniJava.g:7145:1: rule__TerminalExpression__Group_0__1 : rule__TerminalExpression__Group_0__1__Impl ;
    public final void rule__TerminalExpression__Group_0__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7149:1: ( rule__TerminalExpression__Group_0__1__Impl )
            // InternalMiniJava.g:7150:2: rule__TerminalExpression__Group_0__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_0__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_0__1"


    // $ANTLR start "rule__TerminalExpression__Group_0__1__Impl"
    // InternalMiniJava.g:7156:1: rule__TerminalExpression__Group_0__1__Impl : ( ( rule__TerminalExpression__ValueAssignment_0_1 ) ) ;
    public final void rule__TerminalExpression__Group_0__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7160:1: ( ( ( rule__TerminalExpression__ValueAssignment_0_1 ) ) )
            // InternalMiniJava.g:7161:1: ( ( rule__TerminalExpression__ValueAssignment_0_1 ) )
            {
            // InternalMiniJava.g:7161:1: ( ( rule__TerminalExpression__ValueAssignment_0_1 ) )
            // InternalMiniJava.g:7162:2: ( rule__TerminalExpression__ValueAssignment_0_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getValueAssignment_0_1()); 
            }
            // InternalMiniJava.g:7163:2: ( rule__TerminalExpression__ValueAssignment_0_1 )
            // InternalMiniJava.g:7163:3: rule__TerminalExpression__ValueAssignment_0_1
            {
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__ValueAssignment_0_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getValueAssignment_0_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_0__1__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_1__0"
    // InternalMiniJava.g:7172:1: rule__TerminalExpression__Group_1__0 : rule__TerminalExpression__Group_1__0__Impl rule__TerminalExpression__Group_1__1 ;
    public final void rule__TerminalExpression__Group_1__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7176:1: ( rule__TerminalExpression__Group_1__0__Impl rule__TerminalExpression__Group_1__1 )
            // InternalMiniJava.g:7177:2: rule__TerminalExpression__Group_1__0__Impl rule__TerminalExpression__Group_1__1
            {
            pushFollow(FOLLOW_64);
            rule__TerminalExpression__Group_1__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_1__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_1__0"


    // $ANTLR start "rule__TerminalExpression__Group_1__0__Impl"
    // InternalMiniJava.g:7184:1: rule__TerminalExpression__Group_1__0__Impl : ( () ) ;
    public final void rule__TerminalExpression__Group_1__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7188:1: ( ( () ) )
            // InternalMiniJava.g:7189:1: ( () )
            {
            // InternalMiniJava.g:7189:1: ( () )
            // InternalMiniJava.g:7190:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getIntConstantAction_1_0()); 
            }
            // InternalMiniJava.g:7191:2: ()
            // InternalMiniJava.g:7191:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getIntConstantAction_1_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_1__0__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_1__1"
    // InternalMiniJava.g:7199:1: rule__TerminalExpression__Group_1__1 : rule__TerminalExpression__Group_1__1__Impl ;
    public final void rule__TerminalExpression__Group_1__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7203:1: ( rule__TerminalExpression__Group_1__1__Impl )
            // InternalMiniJava.g:7204:2: rule__TerminalExpression__Group_1__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_1__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_1__1"


    // $ANTLR start "rule__TerminalExpression__Group_1__1__Impl"
    // InternalMiniJava.g:7210:1: rule__TerminalExpression__Group_1__1__Impl : ( ( rule__TerminalExpression__ValueAssignment_1_1 ) ) ;
    public final void rule__TerminalExpression__Group_1__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7214:1: ( ( ( rule__TerminalExpression__ValueAssignment_1_1 ) ) )
            // InternalMiniJava.g:7215:1: ( ( rule__TerminalExpression__ValueAssignment_1_1 ) )
            {
            // InternalMiniJava.g:7215:1: ( ( rule__TerminalExpression__ValueAssignment_1_1 ) )
            // InternalMiniJava.g:7216:2: ( rule__TerminalExpression__ValueAssignment_1_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getValueAssignment_1_1()); 
            }
            // InternalMiniJava.g:7217:2: ( rule__TerminalExpression__ValueAssignment_1_1 )
            // InternalMiniJava.g:7217:3: rule__TerminalExpression__ValueAssignment_1_1
            {
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__ValueAssignment_1_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getValueAssignment_1_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_1__1__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_2__0"
    // InternalMiniJava.g:7226:1: rule__TerminalExpression__Group_2__0 : rule__TerminalExpression__Group_2__0__Impl rule__TerminalExpression__Group_2__1 ;
    public final void rule__TerminalExpression__Group_2__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7230:1: ( rule__TerminalExpression__Group_2__0__Impl rule__TerminalExpression__Group_2__1 )
            // InternalMiniJava.g:7231:2: rule__TerminalExpression__Group_2__0__Impl rule__TerminalExpression__Group_2__1
            {
            pushFollow(FOLLOW_65);
            rule__TerminalExpression__Group_2__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_2__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_2__0"


    // $ANTLR start "rule__TerminalExpression__Group_2__0__Impl"
    // InternalMiniJava.g:7238:1: rule__TerminalExpression__Group_2__0__Impl : ( () ) ;
    public final void rule__TerminalExpression__Group_2__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7242:1: ( ( () ) )
            // InternalMiniJava.g:7243:1: ( () )
            {
            // InternalMiniJava.g:7243:1: ( () )
            // InternalMiniJava.g:7244:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getBoolConstantAction_2_0()); 
            }
            // InternalMiniJava.g:7245:2: ()
            // InternalMiniJava.g:7245:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getBoolConstantAction_2_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_2__0__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_2__1"
    // InternalMiniJava.g:7253:1: rule__TerminalExpression__Group_2__1 : rule__TerminalExpression__Group_2__1__Impl ;
    public final void rule__TerminalExpression__Group_2__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7257:1: ( rule__TerminalExpression__Group_2__1__Impl )
            // InternalMiniJava.g:7258:2: rule__TerminalExpression__Group_2__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_2__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_2__1"


    // $ANTLR start "rule__TerminalExpression__Group_2__1__Impl"
    // InternalMiniJava.g:7264:1: rule__TerminalExpression__Group_2__1__Impl : ( ( rule__TerminalExpression__ValueAssignment_2_1 ) ) ;
    public final void rule__TerminalExpression__Group_2__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7268:1: ( ( ( rule__TerminalExpression__ValueAssignment_2_1 ) ) )
            // InternalMiniJava.g:7269:1: ( ( rule__TerminalExpression__ValueAssignment_2_1 ) )
            {
            // InternalMiniJava.g:7269:1: ( ( rule__TerminalExpression__ValueAssignment_2_1 ) )
            // InternalMiniJava.g:7270:2: ( rule__TerminalExpression__ValueAssignment_2_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getValueAssignment_2_1()); 
            }
            // InternalMiniJava.g:7271:2: ( rule__TerminalExpression__ValueAssignment_2_1 )
            // InternalMiniJava.g:7271:3: rule__TerminalExpression__ValueAssignment_2_1
            {
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__ValueAssignment_2_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getValueAssignment_2_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_2__1__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_3__0"
    // InternalMiniJava.g:7280:1: rule__TerminalExpression__Group_3__0 : rule__TerminalExpression__Group_3__0__Impl rule__TerminalExpression__Group_3__1 ;
    public final void rule__TerminalExpression__Group_3__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7284:1: ( rule__TerminalExpression__Group_3__0__Impl rule__TerminalExpression__Group_3__1 )
            // InternalMiniJava.g:7285:2: rule__TerminalExpression__Group_3__0__Impl rule__TerminalExpression__Group_3__1
            {
            pushFollow(FOLLOW_66);
            rule__TerminalExpression__Group_3__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_3__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_3__0"


    // $ANTLR start "rule__TerminalExpression__Group_3__0__Impl"
    // InternalMiniJava.g:7292:1: rule__TerminalExpression__Group_3__0__Impl : ( () ) ;
    public final void rule__TerminalExpression__Group_3__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7296:1: ( ( () ) )
            // InternalMiniJava.g:7297:1: ( () )
            {
            // InternalMiniJava.g:7297:1: ( () )
            // InternalMiniJava.g:7298:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getThisAction_3_0()); 
            }
            // InternalMiniJava.g:7299:2: ()
            // InternalMiniJava.g:7299:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getThisAction_3_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_3__0__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_3__1"
    // InternalMiniJava.g:7307:1: rule__TerminalExpression__Group_3__1 : rule__TerminalExpression__Group_3__1__Impl ;
    public final void rule__TerminalExpression__Group_3__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7311:1: ( rule__TerminalExpression__Group_3__1__Impl )
            // InternalMiniJava.g:7312:2: rule__TerminalExpression__Group_3__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_3__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_3__1"


    // $ANTLR start "rule__TerminalExpression__Group_3__1__Impl"
    // InternalMiniJava.g:7318:1: rule__TerminalExpression__Group_3__1__Impl : ( 'this' ) ;
    public final void rule__TerminalExpression__Group_3__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7322:1: ( ( 'this' ) )
            // InternalMiniJava.g:7323:1: ( 'this' )
            {
            // InternalMiniJava.g:7323:1: ( 'this' )
            // InternalMiniJava.g:7324:2: 'this'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getThisKeyword_3_1()); 
            }
            match(input,59,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getThisKeyword_3_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_3__1__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_4__0"
    // InternalMiniJava.g:7334:1: rule__TerminalExpression__Group_4__0 : rule__TerminalExpression__Group_4__0__Impl rule__TerminalExpression__Group_4__1 ;
    public final void rule__TerminalExpression__Group_4__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7338:1: ( rule__TerminalExpression__Group_4__0__Impl rule__TerminalExpression__Group_4__1 )
            // InternalMiniJava.g:7339:2: rule__TerminalExpression__Group_4__0__Impl rule__TerminalExpression__Group_4__1
            {
            pushFollow(FOLLOW_67);
            rule__TerminalExpression__Group_4__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_4__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_4__0"


    // $ANTLR start "rule__TerminalExpression__Group_4__0__Impl"
    // InternalMiniJava.g:7346:1: rule__TerminalExpression__Group_4__0__Impl : ( () ) ;
    public final void rule__TerminalExpression__Group_4__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7350:1: ( ( () ) )
            // InternalMiniJava.g:7351:1: ( () )
            {
            // InternalMiniJava.g:7351:1: ( () )
            // InternalMiniJava.g:7352:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getSuperAction_4_0()); 
            }
            // InternalMiniJava.g:7353:2: ()
            // InternalMiniJava.g:7353:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getSuperAction_4_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_4__0__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_4__1"
    // InternalMiniJava.g:7361:1: rule__TerminalExpression__Group_4__1 : rule__TerminalExpression__Group_4__1__Impl ;
    public final void rule__TerminalExpression__Group_4__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7365:1: ( rule__TerminalExpression__Group_4__1__Impl )
            // InternalMiniJava.g:7366:2: rule__TerminalExpression__Group_4__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_4__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_4__1"


    // $ANTLR start "rule__TerminalExpression__Group_4__1__Impl"
    // InternalMiniJava.g:7372:1: rule__TerminalExpression__Group_4__1__Impl : ( 'super' ) ;
    public final void rule__TerminalExpression__Group_4__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7376:1: ( ( 'super' ) )
            // InternalMiniJava.g:7377:1: ( 'super' )
            {
            // InternalMiniJava.g:7377:1: ( 'super' )
            // InternalMiniJava.g:7378:2: 'super'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getSuperKeyword_4_1()); 
            }
            match(input,60,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getSuperKeyword_4_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_4__1__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_5__0"
    // InternalMiniJava.g:7388:1: rule__TerminalExpression__Group_5__0 : rule__TerminalExpression__Group_5__0__Impl rule__TerminalExpression__Group_5__1 ;
    public final void rule__TerminalExpression__Group_5__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7392:1: ( rule__TerminalExpression__Group_5__0__Impl rule__TerminalExpression__Group_5__1 )
            // InternalMiniJava.g:7393:2: rule__TerminalExpression__Group_5__0__Impl rule__TerminalExpression__Group_5__1
            {
            pushFollow(FOLLOW_68);
            rule__TerminalExpression__Group_5__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_5__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_5__0"


    // $ANTLR start "rule__TerminalExpression__Group_5__0__Impl"
    // InternalMiniJava.g:7400:1: rule__TerminalExpression__Group_5__0__Impl : ( () ) ;
    public final void rule__TerminalExpression__Group_5__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7404:1: ( ( () ) )
            // InternalMiniJava.g:7405:1: ( () )
            {
            // InternalMiniJava.g:7405:1: ( () )
            // InternalMiniJava.g:7406:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getNullAction_5_0()); 
            }
            // InternalMiniJava.g:7407:2: ()
            // InternalMiniJava.g:7407:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getNullAction_5_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_5__0__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_5__1"
    // InternalMiniJava.g:7415:1: rule__TerminalExpression__Group_5__1 : rule__TerminalExpression__Group_5__1__Impl ;
    public final void rule__TerminalExpression__Group_5__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7419:1: ( rule__TerminalExpression__Group_5__1__Impl )
            // InternalMiniJava.g:7420:2: rule__TerminalExpression__Group_5__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_5__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_5__1"


    // $ANTLR start "rule__TerminalExpression__Group_5__1__Impl"
    // InternalMiniJava.g:7426:1: rule__TerminalExpression__Group_5__1__Impl : ( 'null' ) ;
    public final void rule__TerminalExpression__Group_5__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7430:1: ( ( 'null' ) )
            // InternalMiniJava.g:7431:1: ( 'null' )
            {
            // InternalMiniJava.g:7431:1: ( 'null' )
            // InternalMiniJava.g:7432:2: 'null'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getNullKeyword_5_1()); 
            }
            match(input,61,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getNullKeyword_5_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_5__1__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_6__0"
    // InternalMiniJava.g:7442:1: rule__TerminalExpression__Group_6__0 : rule__TerminalExpression__Group_6__0__Impl rule__TerminalExpression__Group_6__1 ;
    public final void rule__TerminalExpression__Group_6__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7446:1: ( rule__TerminalExpression__Group_6__0__Impl rule__TerminalExpression__Group_6__1 )
            // InternalMiniJava.g:7447:2: rule__TerminalExpression__Group_6__0__Impl rule__TerminalExpression__Group_6__1
            {
            pushFollow(FOLLOW_69);
            rule__TerminalExpression__Group_6__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_6__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_6__0"


    // $ANTLR start "rule__TerminalExpression__Group_6__0__Impl"
    // InternalMiniJava.g:7454:1: rule__TerminalExpression__Group_6__0__Impl : ( () ) ;
    public final void rule__TerminalExpression__Group_6__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7458:1: ( ( () ) )
            // InternalMiniJava.g:7459:1: ( () )
            {
            // InternalMiniJava.g:7459:1: ( () )
            // InternalMiniJava.g:7460:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getNewObjectAction_6_0()); 
            }
            // InternalMiniJava.g:7461:2: ()
            // InternalMiniJava.g:7461:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getNewObjectAction_6_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_6__0__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_6__1"
    // InternalMiniJava.g:7469:1: rule__TerminalExpression__Group_6__1 : rule__TerminalExpression__Group_6__1__Impl rule__TerminalExpression__Group_6__2 ;
    public final void rule__TerminalExpression__Group_6__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7473:1: ( rule__TerminalExpression__Group_6__1__Impl rule__TerminalExpression__Group_6__2 )
            // InternalMiniJava.g:7474:2: rule__TerminalExpression__Group_6__1__Impl rule__TerminalExpression__Group_6__2
            {
            pushFollow(FOLLOW_6);
            rule__TerminalExpression__Group_6__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_6__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_6__1"


    // $ANTLR start "rule__TerminalExpression__Group_6__1__Impl"
    // InternalMiniJava.g:7481:1: rule__TerminalExpression__Group_6__1__Impl : ( 'new' ) ;
    public final void rule__TerminalExpression__Group_6__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7485:1: ( ( 'new' ) )
            // InternalMiniJava.g:7486:1: ( 'new' )
            {
            // InternalMiniJava.g:7486:1: ( 'new' )
            // InternalMiniJava.g:7487:2: 'new'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getNewKeyword_6_1()); 
            }
            match(input,62,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getNewKeyword_6_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_6__1__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_6__2"
    // InternalMiniJava.g:7496:1: rule__TerminalExpression__Group_6__2 : rule__TerminalExpression__Group_6__2__Impl rule__TerminalExpression__Group_6__3 ;
    public final void rule__TerminalExpression__Group_6__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7500:1: ( rule__TerminalExpression__Group_6__2__Impl rule__TerminalExpression__Group_6__3 )
            // InternalMiniJava.g:7501:2: rule__TerminalExpression__Group_6__2__Impl rule__TerminalExpression__Group_6__3
            {
            pushFollow(FOLLOW_31);
            rule__TerminalExpression__Group_6__2__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_6__3();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_6__2"


    // $ANTLR start "rule__TerminalExpression__Group_6__2__Impl"
    // InternalMiniJava.g:7508:1: rule__TerminalExpression__Group_6__2__Impl : ( ( rule__TerminalExpression__TypeAssignment_6_2 ) ) ;
    public final void rule__TerminalExpression__Group_6__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7512:1: ( ( ( rule__TerminalExpression__TypeAssignment_6_2 ) ) )
            // InternalMiniJava.g:7513:1: ( ( rule__TerminalExpression__TypeAssignment_6_2 ) )
            {
            // InternalMiniJava.g:7513:1: ( ( rule__TerminalExpression__TypeAssignment_6_2 ) )
            // InternalMiniJava.g:7514:2: ( rule__TerminalExpression__TypeAssignment_6_2 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getTypeAssignment_6_2()); 
            }
            // InternalMiniJava.g:7515:2: ( rule__TerminalExpression__TypeAssignment_6_2 )
            // InternalMiniJava.g:7515:3: rule__TerminalExpression__TypeAssignment_6_2
            {
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__TypeAssignment_6_2();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getTypeAssignment_6_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_6__2__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_6__3"
    // InternalMiniJava.g:7523:1: rule__TerminalExpression__Group_6__3 : rule__TerminalExpression__Group_6__3__Impl rule__TerminalExpression__Group_6__4 ;
    public final void rule__TerminalExpression__Group_6__3() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7527:1: ( rule__TerminalExpression__Group_6__3__Impl rule__TerminalExpression__Group_6__4 )
            // InternalMiniJava.g:7528:2: rule__TerminalExpression__Group_6__3__Impl rule__TerminalExpression__Group_6__4
            {
            pushFollow(FOLLOW_62);
            rule__TerminalExpression__Group_6__3__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_6__4();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_6__3"


    // $ANTLR start "rule__TerminalExpression__Group_6__3__Impl"
    // InternalMiniJava.g:7535:1: rule__TerminalExpression__Group_6__3__Impl : ( ( '(' ) ) ;
    public final void rule__TerminalExpression__Group_6__3__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7539:1: ( ( ( '(' ) ) )
            // InternalMiniJava.g:7540:1: ( ( '(' ) )
            {
            // InternalMiniJava.g:7540:1: ( ( '(' ) )
            // InternalMiniJava.g:7541:2: ( '(' )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getLeftParenthesisKeyword_6_3()); 
            }
            // InternalMiniJava.g:7542:2: ( '(' )
            // InternalMiniJava.g:7542:3: '('
            {
            match(input,28,FOLLOW_2); if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getLeftParenthesisKeyword_6_3()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_6__3__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_6__4"
    // InternalMiniJava.g:7550:1: rule__TerminalExpression__Group_6__4 : rule__TerminalExpression__Group_6__4__Impl rule__TerminalExpression__Group_6__5 ;
    public final void rule__TerminalExpression__Group_6__4() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7554:1: ( rule__TerminalExpression__Group_6__4__Impl rule__TerminalExpression__Group_6__5 )
            // InternalMiniJava.g:7555:2: rule__TerminalExpression__Group_6__4__Impl rule__TerminalExpression__Group_6__5
            {
            pushFollow(FOLLOW_62);
            rule__TerminalExpression__Group_6__4__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_6__5();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_6__4"


    // $ANTLR start "rule__TerminalExpression__Group_6__4__Impl"
    // InternalMiniJava.g:7562:1: rule__TerminalExpression__Group_6__4__Impl : ( ( rule__TerminalExpression__Group_6_4__0 )? ) ;
    public final void rule__TerminalExpression__Group_6__4__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7566:1: ( ( ( rule__TerminalExpression__Group_6_4__0 )? ) )
            // InternalMiniJava.g:7567:1: ( ( rule__TerminalExpression__Group_6_4__0 )? )
            {
            // InternalMiniJava.g:7567:1: ( ( rule__TerminalExpression__Group_6_4__0 )? )
            // InternalMiniJava.g:7568:2: ( rule__TerminalExpression__Group_6_4__0 )?
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getGroup_6_4()); 
            }
            // InternalMiniJava.g:7569:2: ( rule__TerminalExpression__Group_6_4__0 )?
            int alt55=2;
            int LA55_0 = input.LA(1);

            if ( ((LA55_0>=RULE_ID && LA55_0<=RULE_INT)||(LA55_0>=12 && LA55_0<=13)||LA55_0==28||LA55_0==54||(LA55_0>=58 && LA55_0<=62)) ) {
                alt55=1;
            }
            switch (alt55) {
                case 1 :
                    // InternalMiniJava.g:7569:3: rule__TerminalExpression__Group_6_4__0
                    {
                    pushFollow(FOLLOW_2);
                    rule__TerminalExpression__Group_6_4__0();

                    state._fsp--;
                    if (state.failed) return ;

                    }
                    break;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getGroup_6_4()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_6__4__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_6__5"
    // InternalMiniJava.g:7577:1: rule__TerminalExpression__Group_6__5 : rule__TerminalExpression__Group_6__5__Impl ;
    public final void rule__TerminalExpression__Group_6__5() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7581:1: ( rule__TerminalExpression__Group_6__5__Impl )
            // InternalMiniJava.g:7582:2: rule__TerminalExpression__Group_6__5__Impl
            {
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_6__5__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_6__5"


    // $ANTLR start "rule__TerminalExpression__Group_6__5__Impl"
    // InternalMiniJava.g:7588:1: rule__TerminalExpression__Group_6__5__Impl : ( ')' ) ;
    public final void rule__TerminalExpression__Group_6__5__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7592:1: ( ( ')' ) )
            // InternalMiniJava.g:7593:1: ( ')' )
            {
            // InternalMiniJava.g:7593:1: ( ')' )
            // InternalMiniJava.g:7594:2: ')'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getRightParenthesisKeyword_6_5()); 
            }
            match(input,29,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getRightParenthesisKeyword_6_5()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_6__5__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_6_4__0"
    // InternalMiniJava.g:7604:1: rule__TerminalExpression__Group_6_4__0 : rule__TerminalExpression__Group_6_4__0__Impl rule__TerminalExpression__Group_6_4__1 ;
    public final void rule__TerminalExpression__Group_6_4__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7608:1: ( rule__TerminalExpression__Group_6_4__0__Impl rule__TerminalExpression__Group_6_4__1 )
            // InternalMiniJava.g:7609:2: rule__TerminalExpression__Group_6_4__0__Impl rule__TerminalExpression__Group_6_4__1
            {
            pushFollow(FOLLOW_15);
            rule__TerminalExpression__Group_6_4__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_6_4__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_6_4__0"


    // $ANTLR start "rule__TerminalExpression__Group_6_4__0__Impl"
    // InternalMiniJava.g:7616:1: rule__TerminalExpression__Group_6_4__0__Impl : ( ( rule__TerminalExpression__ArgsAssignment_6_4_0 ) ) ;
    public final void rule__TerminalExpression__Group_6_4__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7620:1: ( ( ( rule__TerminalExpression__ArgsAssignment_6_4_0 ) ) )
            // InternalMiniJava.g:7621:1: ( ( rule__TerminalExpression__ArgsAssignment_6_4_0 ) )
            {
            // InternalMiniJava.g:7621:1: ( ( rule__TerminalExpression__ArgsAssignment_6_4_0 ) )
            // InternalMiniJava.g:7622:2: ( rule__TerminalExpression__ArgsAssignment_6_4_0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getArgsAssignment_6_4_0()); 
            }
            // InternalMiniJava.g:7623:2: ( rule__TerminalExpression__ArgsAssignment_6_4_0 )
            // InternalMiniJava.g:7623:3: rule__TerminalExpression__ArgsAssignment_6_4_0
            {
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__ArgsAssignment_6_4_0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getArgsAssignment_6_4_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_6_4__0__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_6_4__1"
    // InternalMiniJava.g:7631:1: rule__TerminalExpression__Group_6_4__1 : rule__TerminalExpression__Group_6_4__1__Impl ;
    public final void rule__TerminalExpression__Group_6_4__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7635:1: ( rule__TerminalExpression__Group_6_4__1__Impl )
            // InternalMiniJava.g:7636:2: rule__TerminalExpression__Group_6_4__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_6_4__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_6_4__1"


    // $ANTLR start "rule__TerminalExpression__Group_6_4__1__Impl"
    // InternalMiniJava.g:7642:1: rule__TerminalExpression__Group_6_4__1__Impl : ( ( rule__TerminalExpression__Group_6_4_1__0 )* ) ;
    public final void rule__TerminalExpression__Group_6_4__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7646:1: ( ( ( rule__TerminalExpression__Group_6_4_1__0 )* ) )
            // InternalMiniJava.g:7647:1: ( ( rule__TerminalExpression__Group_6_4_1__0 )* )
            {
            // InternalMiniJava.g:7647:1: ( ( rule__TerminalExpression__Group_6_4_1__0 )* )
            // InternalMiniJava.g:7648:2: ( rule__TerminalExpression__Group_6_4_1__0 )*
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getGroup_6_4_1()); 
            }
            // InternalMiniJava.g:7649:2: ( rule__TerminalExpression__Group_6_4_1__0 )*
            loop56:
            do {
                int alt56=2;
                int LA56_0 = input.LA(1);

                if ( (LA56_0==26) ) {
                    alt56=1;
                }


                switch (alt56) {
            	case 1 :
            	    // InternalMiniJava.g:7649:3: rule__TerminalExpression__Group_6_4_1__0
            	    {
            	    pushFollow(FOLLOW_16);
            	    rule__TerminalExpression__Group_6_4_1__0();

            	    state._fsp--;
            	    if (state.failed) return ;

            	    }
            	    break;

            	default :
            	    break loop56;
                }
            } while (true);

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getGroup_6_4_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_6_4__1__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_6_4_1__0"
    // InternalMiniJava.g:7658:1: rule__TerminalExpression__Group_6_4_1__0 : rule__TerminalExpression__Group_6_4_1__0__Impl rule__TerminalExpression__Group_6_4_1__1 ;
    public final void rule__TerminalExpression__Group_6_4_1__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7662:1: ( rule__TerminalExpression__Group_6_4_1__0__Impl rule__TerminalExpression__Group_6_4_1__1 )
            // InternalMiniJava.g:7663:2: rule__TerminalExpression__Group_6_4_1__0__Impl rule__TerminalExpression__Group_6_4_1__1
            {
            pushFollow(FOLLOW_25);
            rule__TerminalExpression__Group_6_4_1__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_6_4_1__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_6_4_1__0"


    // $ANTLR start "rule__TerminalExpression__Group_6_4_1__0__Impl"
    // InternalMiniJava.g:7670:1: rule__TerminalExpression__Group_6_4_1__0__Impl : ( ',' ) ;
    public final void rule__TerminalExpression__Group_6_4_1__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7674:1: ( ( ',' ) )
            // InternalMiniJava.g:7675:1: ( ',' )
            {
            // InternalMiniJava.g:7675:1: ( ',' )
            // InternalMiniJava.g:7676:2: ','
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getCommaKeyword_6_4_1_0()); 
            }
            match(input,26,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getCommaKeyword_6_4_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_6_4_1__0__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_6_4_1__1"
    // InternalMiniJava.g:7685:1: rule__TerminalExpression__Group_6_4_1__1 : rule__TerminalExpression__Group_6_4_1__1__Impl ;
    public final void rule__TerminalExpression__Group_6_4_1__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7689:1: ( rule__TerminalExpression__Group_6_4_1__1__Impl )
            // InternalMiniJava.g:7690:2: rule__TerminalExpression__Group_6_4_1__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_6_4_1__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_6_4_1__1"


    // $ANTLR start "rule__TerminalExpression__Group_6_4_1__1__Impl"
    // InternalMiniJava.g:7696:1: rule__TerminalExpression__Group_6_4_1__1__Impl : ( ( rule__TerminalExpression__ArgsAssignment_6_4_1_1 ) ) ;
    public final void rule__TerminalExpression__Group_6_4_1__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7700:1: ( ( ( rule__TerminalExpression__ArgsAssignment_6_4_1_1 ) ) )
            // InternalMiniJava.g:7701:1: ( ( rule__TerminalExpression__ArgsAssignment_6_4_1_1 ) )
            {
            // InternalMiniJava.g:7701:1: ( ( rule__TerminalExpression__ArgsAssignment_6_4_1_1 ) )
            // InternalMiniJava.g:7702:2: ( rule__TerminalExpression__ArgsAssignment_6_4_1_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getArgsAssignment_6_4_1_1()); 
            }
            // InternalMiniJava.g:7703:2: ( rule__TerminalExpression__ArgsAssignment_6_4_1_1 )
            // InternalMiniJava.g:7703:3: rule__TerminalExpression__ArgsAssignment_6_4_1_1
            {
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__ArgsAssignment_6_4_1_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getArgsAssignment_6_4_1_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_6_4_1__1__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_7__0"
    // InternalMiniJava.g:7712:1: rule__TerminalExpression__Group_7__0 : rule__TerminalExpression__Group_7__0__Impl rule__TerminalExpression__Group_7__1 ;
    public final void rule__TerminalExpression__Group_7__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7716:1: ( rule__TerminalExpression__Group_7__0__Impl rule__TerminalExpression__Group_7__1 )
            // InternalMiniJava.g:7717:2: rule__TerminalExpression__Group_7__0__Impl rule__TerminalExpression__Group_7__1
            {
            pushFollow(FOLLOW_69);
            rule__TerminalExpression__Group_7__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_7__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_7__0"


    // $ANTLR start "rule__TerminalExpression__Group_7__0__Impl"
    // InternalMiniJava.g:7724:1: rule__TerminalExpression__Group_7__0__Impl : ( () ) ;
    public final void rule__TerminalExpression__Group_7__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7728:1: ( ( () ) )
            // InternalMiniJava.g:7729:1: ( () )
            {
            // InternalMiniJava.g:7729:1: ( () )
            // InternalMiniJava.g:7730:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getNewArrayAction_7_0()); 
            }
            // InternalMiniJava.g:7731:2: ()
            // InternalMiniJava.g:7731:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getNewArrayAction_7_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_7__0__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_7__1"
    // InternalMiniJava.g:7739:1: rule__TerminalExpression__Group_7__1 : rule__TerminalExpression__Group_7__1__Impl rule__TerminalExpression__Group_7__2 ;
    public final void rule__TerminalExpression__Group_7__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7743:1: ( rule__TerminalExpression__Group_7__1__Impl rule__TerminalExpression__Group_7__2 )
            // InternalMiniJava.g:7744:2: rule__TerminalExpression__Group_7__1__Impl rule__TerminalExpression__Group_7__2
            {
            pushFollow(FOLLOW_23);
            rule__TerminalExpression__Group_7__1__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_7__2();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_7__1"


    // $ANTLR start "rule__TerminalExpression__Group_7__1__Impl"
    // InternalMiniJava.g:7751:1: rule__TerminalExpression__Group_7__1__Impl : ( 'new' ) ;
    public final void rule__TerminalExpression__Group_7__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7755:1: ( ( 'new' ) )
            // InternalMiniJava.g:7756:1: ( 'new' )
            {
            // InternalMiniJava.g:7756:1: ( 'new' )
            // InternalMiniJava.g:7757:2: 'new'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getNewKeyword_7_1()); 
            }
            match(input,62,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getNewKeyword_7_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_7__1__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_7__2"
    // InternalMiniJava.g:7766:1: rule__TerminalExpression__Group_7__2 : rule__TerminalExpression__Group_7__2__Impl rule__TerminalExpression__Group_7__3 ;
    public final void rule__TerminalExpression__Group_7__2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7770:1: ( rule__TerminalExpression__Group_7__2__Impl rule__TerminalExpression__Group_7__3 )
            // InternalMiniJava.g:7771:2: rule__TerminalExpression__Group_7__2__Impl rule__TerminalExpression__Group_7__3
            {
            pushFollow(FOLLOW_35);
            rule__TerminalExpression__Group_7__2__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_7__3();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_7__2"


    // $ANTLR start "rule__TerminalExpression__Group_7__2__Impl"
    // InternalMiniJava.g:7778:1: rule__TerminalExpression__Group_7__2__Impl : ( ( rule__TerminalExpression__TypeAssignment_7_2 ) ) ;
    public final void rule__TerminalExpression__Group_7__2__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7782:1: ( ( ( rule__TerminalExpression__TypeAssignment_7_2 ) ) )
            // InternalMiniJava.g:7783:1: ( ( rule__TerminalExpression__TypeAssignment_7_2 ) )
            {
            // InternalMiniJava.g:7783:1: ( ( rule__TerminalExpression__TypeAssignment_7_2 ) )
            // InternalMiniJava.g:7784:2: ( rule__TerminalExpression__TypeAssignment_7_2 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getTypeAssignment_7_2()); 
            }
            // InternalMiniJava.g:7785:2: ( rule__TerminalExpression__TypeAssignment_7_2 )
            // InternalMiniJava.g:7785:3: rule__TerminalExpression__TypeAssignment_7_2
            {
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__TypeAssignment_7_2();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getTypeAssignment_7_2()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_7__2__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_7__3"
    // InternalMiniJava.g:7793:1: rule__TerminalExpression__Group_7__3 : rule__TerminalExpression__Group_7__3__Impl rule__TerminalExpression__Group_7__4 ;
    public final void rule__TerminalExpression__Group_7__3() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7797:1: ( rule__TerminalExpression__Group_7__3__Impl rule__TerminalExpression__Group_7__4 )
            // InternalMiniJava.g:7798:2: rule__TerminalExpression__Group_7__3__Impl rule__TerminalExpression__Group_7__4
            {
            pushFollow(FOLLOW_25);
            rule__TerminalExpression__Group_7__3__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_7__4();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_7__3"


    // $ANTLR start "rule__TerminalExpression__Group_7__3__Impl"
    // InternalMiniJava.g:7805:1: rule__TerminalExpression__Group_7__3__Impl : ( ( '[' ) ) ;
    public final void rule__TerminalExpression__Group_7__3__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7809:1: ( ( ( '[' ) ) )
            // InternalMiniJava.g:7810:1: ( ( '[' ) )
            {
            // InternalMiniJava.g:7810:1: ( ( '[' ) )
            // InternalMiniJava.g:7811:2: ( '[' )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getLeftSquareBracketKeyword_7_3()); 
            }
            // InternalMiniJava.g:7812:2: ( '[' )
            // InternalMiniJava.g:7812:3: '['
            {
            match(input,39,FOLLOW_2); if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getLeftSquareBracketKeyword_7_3()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_7__3__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_7__4"
    // InternalMiniJava.g:7820:1: rule__TerminalExpression__Group_7__4 : rule__TerminalExpression__Group_7__4__Impl rule__TerminalExpression__Group_7__5 ;
    public final void rule__TerminalExpression__Group_7__4() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7824:1: ( rule__TerminalExpression__Group_7__4__Impl rule__TerminalExpression__Group_7__5 )
            // InternalMiniJava.g:7825:2: rule__TerminalExpression__Group_7__4__Impl rule__TerminalExpression__Group_7__5
            {
            pushFollow(FOLLOW_36);
            rule__TerminalExpression__Group_7__4__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_7__5();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_7__4"


    // $ANTLR start "rule__TerminalExpression__Group_7__4__Impl"
    // InternalMiniJava.g:7832:1: rule__TerminalExpression__Group_7__4__Impl : ( ( rule__TerminalExpression__SizeAssignment_7_4 ) ) ;
    public final void rule__TerminalExpression__Group_7__4__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7836:1: ( ( ( rule__TerminalExpression__SizeAssignment_7_4 ) ) )
            // InternalMiniJava.g:7837:1: ( ( rule__TerminalExpression__SizeAssignment_7_4 ) )
            {
            // InternalMiniJava.g:7837:1: ( ( rule__TerminalExpression__SizeAssignment_7_4 ) )
            // InternalMiniJava.g:7838:2: ( rule__TerminalExpression__SizeAssignment_7_4 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getSizeAssignment_7_4()); 
            }
            // InternalMiniJava.g:7839:2: ( rule__TerminalExpression__SizeAssignment_7_4 )
            // InternalMiniJava.g:7839:3: rule__TerminalExpression__SizeAssignment_7_4
            {
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__SizeAssignment_7_4();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getSizeAssignment_7_4()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_7__4__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_7__5"
    // InternalMiniJava.g:7847:1: rule__TerminalExpression__Group_7__5 : rule__TerminalExpression__Group_7__5__Impl ;
    public final void rule__TerminalExpression__Group_7__5() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7851:1: ( rule__TerminalExpression__Group_7__5__Impl )
            // InternalMiniJava.g:7852:2: rule__TerminalExpression__Group_7__5__Impl
            {
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_7__5__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_7__5"


    // $ANTLR start "rule__TerminalExpression__Group_7__5__Impl"
    // InternalMiniJava.g:7858:1: rule__TerminalExpression__Group_7__5__Impl : ( ']' ) ;
    public final void rule__TerminalExpression__Group_7__5__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7862:1: ( ( ']' ) )
            // InternalMiniJava.g:7863:1: ( ']' )
            {
            // InternalMiniJava.g:7863:1: ( ']' )
            // InternalMiniJava.g:7864:2: ']'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getRightSquareBracketKeyword_7_5()); 
            }
            match(input,40,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getRightSquareBracketKeyword_7_5()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_7__5__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_8__0"
    // InternalMiniJava.g:7874:1: rule__TerminalExpression__Group_8__0 : rule__TerminalExpression__Group_8__0__Impl rule__TerminalExpression__Group_8__1 ;
    public final void rule__TerminalExpression__Group_8__0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7878:1: ( rule__TerminalExpression__Group_8__0__Impl rule__TerminalExpression__Group_8__1 )
            // InternalMiniJava.g:7879:2: rule__TerminalExpression__Group_8__0__Impl rule__TerminalExpression__Group_8__1
            {
            pushFollow(FOLLOW_25);
            rule__TerminalExpression__Group_8__0__Impl();

            state._fsp--;
            if (state.failed) return ;
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_8__1();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_8__0"


    // $ANTLR start "rule__TerminalExpression__Group_8__0__Impl"
    // InternalMiniJava.g:7886:1: rule__TerminalExpression__Group_8__0__Impl : ( () ) ;
    public final void rule__TerminalExpression__Group_8__0__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7890:1: ( ( () ) )
            // InternalMiniJava.g:7891:1: ( () )
            {
            // InternalMiniJava.g:7891:1: ( () )
            // InternalMiniJava.g:7892:2: ()
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getSymbolRefAction_8_0()); 
            }
            // InternalMiniJava.g:7893:2: ()
            // InternalMiniJava.g:7893:3: 
            {
            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getSymbolRefAction_8_0()); 
            }

            }


            }

        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_8__0__Impl"


    // $ANTLR start "rule__TerminalExpression__Group_8__1"
    // InternalMiniJava.g:7901:1: rule__TerminalExpression__Group_8__1 : rule__TerminalExpression__Group_8__1__Impl ;
    public final void rule__TerminalExpression__Group_8__1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7905:1: ( rule__TerminalExpression__Group_8__1__Impl )
            // InternalMiniJava.g:7906:2: rule__TerminalExpression__Group_8__1__Impl
            {
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__Group_8__1__Impl();

            state._fsp--;
            if (state.failed) return ;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_8__1"


    // $ANTLR start "rule__TerminalExpression__Group_8__1__Impl"
    // InternalMiniJava.g:7912:1: rule__TerminalExpression__Group_8__1__Impl : ( ( rule__TerminalExpression__SymbolAssignment_8_1 ) ) ;
    public final void rule__TerminalExpression__Group_8__1__Impl() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7916:1: ( ( ( rule__TerminalExpression__SymbolAssignment_8_1 ) ) )
            // InternalMiniJava.g:7917:1: ( ( rule__TerminalExpression__SymbolAssignment_8_1 ) )
            {
            // InternalMiniJava.g:7917:1: ( ( rule__TerminalExpression__SymbolAssignment_8_1 ) )
            // InternalMiniJava.g:7918:2: ( rule__TerminalExpression__SymbolAssignment_8_1 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getSymbolAssignment_8_1()); 
            }
            // InternalMiniJava.g:7919:2: ( rule__TerminalExpression__SymbolAssignment_8_1 )
            // InternalMiniJava.g:7919:3: rule__TerminalExpression__SymbolAssignment_8_1
            {
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__SymbolAssignment_8_1();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getSymbolAssignment_8_1()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__Group_8__1__Impl"


    // $ANTLR start "rule__Program__NameAssignment_0_1"
    // InternalMiniJava.g:7928:1: rule__Program__NameAssignment_0_1 : ( ruleQualifiedName ) ;
    public final void rule__Program__NameAssignment_0_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7932:1: ( ( ruleQualifiedName ) )
            // InternalMiniJava.g:7933:2: ( ruleQualifiedName )
            {
            // InternalMiniJava.g:7933:2: ( ruleQualifiedName )
            // InternalMiniJava.g:7934:3: ruleQualifiedName
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getProgramAccess().getNameQualifiedNameParserRuleCall_0_1_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleQualifiedName();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getProgramAccess().getNameQualifiedNameParserRuleCall_0_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Program__NameAssignment_0_1"


    // $ANTLR start "rule__Program__ImportsAssignment_1"
    // InternalMiniJava.g:7943:1: rule__Program__ImportsAssignment_1 : ( ruleImport ) ;
    public final void rule__Program__ImportsAssignment_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7947:1: ( ( ruleImport ) )
            // InternalMiniJava.g:7948:2: ( ruleImport )
            {
            // InternalMiniJava.g:7948:2: ( ruleImport )
            // InternalMiniJava.g:7949:3: ruleImport
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getProgramAccess().getImportsImportParserRuleCall_1_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleImport();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getProgramAccess().getImportsImportParserRuleCall_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Program__ImportsAssignment_1"


    // $ANTLR start "rule__Program__ClassesAssignment_2"
    // InternalMiniJava.g:7958:1: rule__Program__ClassesAssignment_2 : ( ruleTypeDeclaration ) ;
    public final void rule__Program__ClassesAssignment_2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7962:1: ( ( ruleTypeDeclaration ) )
            // InternalMiniJava.g:7963:2: ( ruleTypeDeclaration )
            {
            // InternalMiniJava.g:7963:2: ( ruleTypeDeclaration )
            // InternalMiniJava.g:7964:3: ruleTypeDeclaration
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getProgramAccess().getClassesTypeDeclarationParserRuleCall_2_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleTypeDeclaration();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getProgramAccess().getClassesTypeDeclarationParserRuleCall_2_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Program__ClassesAssignment_2"


    // $ANTLR start "rule__Import__ImportedNamespaceAssignment_1"
    // InternalMiniJava.g:7973:1: rule__Import__ImportedNamespaceAssignment_1 : ( ruleQualifiedNameWithWildcard ) ;
    public final void rule__Import__ImportedNamespaceAssignment_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7977:1: ( ( ruleQualifiedNameWithWildcard ) )
            // InternalMiniJava.g:7978:2: ( ruleQualifiedNameWithWildcard )
            {
            // InternalMiniJava.g:7978:2: ( ruleQualifiedNameWithWildcard )
            // InternalMiniJava.g:7979:3: ruleQualifiedNameWithWildcard
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getImportAccess().getImportedNamespaceQualifiedNameWithWildcardParserRuleCall_1_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleQualifiedNameWithWildcard();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getImportAccess().getImportedNamespaceQualifiedNameWithWildcardParserRuleCall_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Import__ImportedNamespaceAssignment_1"


    // $ANTLR start "rule__Class__AccessLevelAssignment_0"
    // InternalMiniJava.g:7988:1: rule__Class__AccessLevelAssignment_0 : ( ruleAccessLevel ) ;
    public final void rule__Class__AccessLevelAssignment_0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:7992:1: ( ( ruleAccessLevel ) )
            // InternalMiniJava.g:7993:2: ( ruleAccessLevel )
            {
            // InternalMiniJava.g:7993:2: ( ruleAccessLevel )
            // InternalMiniJava.g:7994:3: ruleAccessLevel
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getAccessLevelAccessLevelEnumRuleCall_0_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleAccessLevel();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getAccessLevelAccessLevelEnumRuleCall_0_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__AccessLevelAssignment_0"


    // $ANTLR start "rule__Class__AbstractAssignment_1"
    // InternalMiniJava.g:8003:1: rule__Class__AbstractAssignment_1 : ( ( 'abstract' ) ) ;
    public final void rule__Class__AbstractAssignment_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8007:1: ( ( ( 'abstract' ) ) )
            // InternalMiniJava.g:8008:2: ( ( 'abstract' ) )
            {
            // InternalMiniJava.g:8008:2: ( ( 'abstract' ) )
            // InternalMiniJava.g:8009:3: ( 'abstract' )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getAbstractAbstractKeyword_1_0()); 
            }
            // InternalMiniJava.g:8010:3: ( 'abstract' )
            // InternalMiniJava.g:8011:4: 'abstract'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getAbstractAbstractKeyword_1_0()); 
            }
            match(input,63,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getAbstractAbstractKeyword_1_0()); 
            }

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getAbstractAbstractKeyword_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__AbstractAssignment_1"


    // $ANTLR start "rule__Class__NameAssignment_3"
    // InternalMiniJava.g:8022:1: rule__Class__NameAssignment_3 : ( RULE_ID ) ;
    public final void rule__Class__NameAssignment_3() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8026:1: ( ( RULE_ID ) )
            // InternalMiniJava.g:8027:2: ( RULE_ID )
            {
            // InternalMiniJava.g:8027:2: ( RULE_ID )
            // InternalMiniJava.g:8028:3: RULE_ID
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getNameIDTerminalRuleCall_3_0()); 
            }
            match(input,RULE_ID,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getNameIDTerminalRuleCall_3_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__NameAssignment_3"


    // $ANTLR start "rule__Class__SuperClassAssignment_4_1"
    // InternalMiniJava.g:8037:1: rule__Class__SuperClassAssignment_4_1 : ( ( ruleQualifiedName ) ) ;
    public final void rule__Class__SuperClassAssignment_4_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8041:1: ( ( ( ruleQualifiedName ) ) )
            // InternalMiniJava.g:8042:2: ( ( ruleQualifiedName ) )
            {
            // InternalMiniJava.g:8042:2: ( ( ruleQualifiedName ) )
            // InternalMiniJava.g:8043:3: ( ruleQualifiedName )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getSuperClassClassCrossReference_4_1_0()); 
            }
            // InternalMiniJava.g:8044:3: ( ruleQualifiedName )
            // InternalMiniJava.g:8045:4: ruleQualifiedName
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getSuperClassClassQualifiedNameParserRuleCall_4_1_0_1()); 
            }
            pushFollow(FOLLOW_2);
            ruleQualifiedName();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getSuperClassClassQualifiedNameParserRuleCall_4_1_0_1()); 
            }

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getSuperClassClassCrossReference_4_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__SuperClassAssignment_4_1"


    // $ANTLR start "rule__Class__ImplementsAssignment_5_1"
    // InternalMiniJava.g:8056:1: rule__Class__ImplementsAssignment_5_1 : ( ( ruleQualifiedName ) ) ;
    public final void rule__Class__ImplementsAssignment_5_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8060:1: ( ( ( ruleQualifiedName ) ) )
            // InternalMiniJava.g:8061:2: ( ( ruleQualifiedName ) )
            {
            // InternalMiniJava.g:8061:2: ( ( ruleQualifiedName ) )
            // InternalMiniJava.g:8062:3: ( ruleQualifiedName )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getImplementsInterfaceCrossReference_5_1_0()); 
            }
            // InternalMiniJava.g:8063:3: ( ruleQualifiedName )
            // InternalMiniJava.g:8064:4: ruleQualifiedName
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getImplementsInterfaceQualifiedNameParserRuleCall_5_1_0_1()); 
            }
            pushFollow(FOLLOW_2);
            ruleQualifiedName();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getImplementsInterfaceQualifiedNameParserRuleCall_5_1_0_1()); 
            }

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getImplementsInterfaceCrossReference_5_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__ImplementsAssignment_5_1"


    // $ANTLR start "rule__Class__ImplementsAssignment_5_2_1"
    // InternalMiniJava.g:8075:1: rule__Class__ImplementsAssignment_5_2_1 : ( ( ruleQualifiedName ) ) ;
    public final void rule__Class__ImplementsAssignment_5_2_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8079:1: ( ( ( ruleQualifiedName ) ) )
            // InternalMiniJava.g:8080:2: ( ( ruleQualifiedName ) )
            {
            // InternalMiniJava.g:8080:2: ( ( ruleQualifiedName ) )
            // InternalMiniJava.g:8081:3: ( ruleQualifiedName )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getImplementsInterfaceCrossReference_5_2_1_0()); 
            }
            // InternalMiniJava.g:8082:3: ( ruleQualifiedName )
            // InternalMiniJava.g:8083:4: ruleQualifiedName
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getImplementsInterfaceQualifiedNameParserRuleCall_5_2_1_0_1()); 
            }
            pushFollow(FOLLOW_2);
            ruleQualifiedName();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getImplementsInterfaceQualifiedNameParserRuleCall_5_2_1_0_1()); 
            }

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getImplementsInterfaceCrossReference_5_2_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__ImplementsAssignment_5_2_1"


    // $ANTLR start "rule__Class__MembersAssignment_7"
    // InternalMiniJava.g:8094:1: rule__Class__MembersAssignment_7 : ( ruleMember ) ;
    public final void rule__Class__MembersAssignment_7() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8098:1: ( ( ruleMember ) )
            // InternalMiniJava.g:8099:2: ( ruleMember )
            {
            // InternalMiniJava.g:8099:2: ( ruleMember )
            // InternalMiniJava.g:8100:3: ruleMember
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassAccess().getMembersMemberParserRuleCall_7_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleMember();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassAccess().getMembersMemberParserRuleCall_7_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Class__MembersAssignment_7"


    // $ANTLR start "rule__Interface__AccessLevelAssignment_0"
    // InternalMiniJava.g:8109:1: rule__Interface__AccessLevelAssignment_0 : ( ruleAccessLevel ) ;
    public final void rule__Interface__AccessLevelAssignment_0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8113:1: ( ( ruleAccessLevel ) )
            // InternalMiniJava.g:8114:2: ( ruleAccessLevel )
            {
            // InternalMiniJava.g:8114:2: ( ruleAccessLevel )
            // InternalMiniJava.g:8115:3: ruleAccessLevel
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getInterfaceAccess().getAccessLevelAccessLevelEnumRuleCall_0_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleAccessLevel();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getInterfaceAccess().getAccessLevelAccessLevelEnumRuleCall_0_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__AccessLevelAssignment_0"


    // $ANTLR start "rule__Interface__NameAssignment_2"
    // InternalMiniJava.g:8124:1: rule__Interface__NameAssignment_2 : ( RULE_ID ) ;
    public final void rule__Interface__NameAssignment_2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8128:1: ( ( RULE_ID ) )
            // InternalMiniJava.g:8129:2: ( RULE_ID )
            {
            // InternalMiniJava.g:8129:2: ( RULE_ID )
            // InternalMiniJava.g:8130:3: RULE_ID
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getInterfaceAccess().getNameIDTerminalRuleCall_2_0()); 
            }
            match(input,RULE_ID,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getInterfaceAccess().getNameIDTerminalRuleCall_2_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__NameAssignment_2"


    // $ANTLR start "rule__Interface__ImplementsAssignment_3_1"
    // InternalMiniJava.g:8139:1: rule__Interface__ImplementsAssignment_3_1 : ( ( ruleQualifiedName ) ) ;
    public final void rule__Interface__ImplementsAssignment_3_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8143:1: ( ( ( ruleQualifiedName ) ) )
            // InternalMiniJava.g:8144:2: ( ( ruleQualifiedName ) )
            {
            // InternalMiniJava.g:8144:2: ( ( ruleQualifiedName ) )
            // InternalMiniJava.g:8145:3: ( ruleQualifiedName )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getInterfaceAccess().getImplementsInterfaceCrossReference_3_1_0()); 
            }
            // InternalMiniJava.g:8146:3: ( ruleQualifiedName )
            // InternalMiniJava.g:8147:4: ruleQualifiedName
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getInterfaceAccess().getImplementsInterfaceQualifiedNameParserRuleCall_3_1_0_1()); 
            }
            pushFollow(FOLLOW_2);
            ruleQualifiedName();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getInterfaceAccess().getImplementsInterfaceQualifiedNameParserRuleCall_3_1_0_1()); 
            }

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getInterfaceAccess().getImplementsInterfaceCrossReference_3_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__ImplementsAssignment_3_1"


    // $ANTLR start "rule__Interface__ImplementsAssignment_3_2_1"
    // InternalMiniJava.g:8158:1: rule__Interface__ImplementsAssignment_3_2_1 : ( ( ruleQualifiedName ) ) ;
    public final void rule__Interface__ImplementsAssignment_3_2_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8162:1: ( ( ( ruleQualifiedName ) ) )
            // InternalMiniJava.g:8163:2: ( ( ruleQualifiedName ) )
            {
            // InternalMiniJava.g:8163:2: ( ( ruleQualifiedName ) )
            // InternalMiniJava.g:8164:3: ( ruleQualifiedName )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getInterfaceAccess().getImplementsInterfaceCrossReference_3_2_1_0()); 
            }
            // InternalMiniJava.g:8165:3: ( ruleQualifiedName )
            // InternalMiniJava.g:8166:4: ruleQualifiedName
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getInterfaceAccess().getImplementsInterfaceQualifiedNameParserRuleCall_3_2_1_0_1()); 
            }
            pushFollow(FOLLOW_2);
            ruleQualifiedName();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getInterfaceAccess().getImplementsInterfaceQualifiedNameParserRuleCall_3_2_1_0_1()); 
            }

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getInterfaceAccess().getImplementsInterfaceCrossReference_3_2_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__ImplementsAssignment_3_2_1"


    // $ANTLR start "rule__Interface__MembersAssignment_5"
    // InternalMiniJava.g:8177:1: rule__Interface__MembersAssignment_5 : ( ruleMember ) ;
    public final void rule__Interface__MembersAssignment_5() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8181:1: ( ( ruleMember ) )
            // InternalMiniJava.g:8182:2: ( ruleMember )
            {
            // InternalMiniJava.g:8182:2: ( ruleMember )
            // InternalMiniJava.g:8183:3: ruleMember
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getInterfaceAccess().getMembersMemberParserRuleCall_5_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleMember();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getInterfaceAccess().getMembersMemberParserRuleCall_5_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Interface__MembersAssignment_5"


    // $ANTLR start "rule__Method__AccessAssignment_0"
    // InternalMiniJava.g:8192:1: rule__Method__AccessAssignment_0 : ( ruleAccessLevel ) ;
    public final void rule__Method__AccessAssignment_0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8196:1: ( ( ruleAccessLevel ) )
            // InternalMiniJava.g:8197:2: ( ruleAccessLevel )
            {
            // InternalMiniJava.g:8197:2: ( ruleAccessLevel )
            // InternalMiniJava.g:8198:3: ruleAccessLevel
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getAccessAccessLevelEnumRuleCall_0_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleAccessLevel();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getAccessAccessLevelEnumRuleCall_0_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__AccessAssignment_0"


    // $ANTLR start "rule__Method__AbstractAssignment_1"
    // InternalMiniJava.g:8207:1: rule__Method__AbstractAssignment_1 : ( ( 'abstract' ) ) ;
    public final void rule__Method__AbstractAssignment_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8211:1: ( ( ( 'abstract' ) ) )
            // InternalMiniJava.g:8212:2: ( ( 'abstract' ) )
            {
            // InternalMiniJava.g:8212:2: ( ( 'abstract' ) )
            // InternalMiniJava.g:8213:3: ( 'abstract' )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getAbstractAbstractKeyword_1_0()); 
            }
            // InternalMiniJava.g:8214:3: ( 'abstract' )
            // InternalMiniJava.g:8215:4: 'abstract'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getAbstractAbstractKeyword_1_0()); 
            }
            match(input,63,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getAbstractAbstractKeyword_1_0()); 
            }

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getAbstractAbstractKeyword_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__AbstractAssignment_1"


    // $ANTLR start "rule__Method__StaticAssignment_2"
    // InternalMiniJava.g:8226:1: rule__Method__StaticAssignment_2 : ( ( 'static' ) ) ;
    public final void rule__Method__StaticAssignment_2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8230:1: ( ( ( 'static' ) ) )
            // InternalMiniJava.g:8231:2: ( ( 'static' ) )
            {
            // InternalMiniJava.g:8231:2: ( ( 'static' ) )
            // InternalMiniJava.g:8232:3: ( 'static' )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getStaticStaticKeyword_2_0()); 
            }
            // InternalMiniJava.g:8233:3: ( 'static' )
            // InternalMiniJava.g:8234:4: 'static'
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getStaticStaticKeyword_2_0()); 
            }
            match(input,64,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getStaticStaticKeyword_2_0()); 
            }

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getStaticStaticKeyword_2_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__StaticAssignment_2"


    // $ANTLR start "rule__Method__TypeRefAssignment_3"
    // InternalMiniJava.g:8245:1: rule__Method__TypeRefAssignment_3 : ( ruleTypeRef ) ;
    public final void rule__Method__TypeRefAssignment_3() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8249:1: ( ( ruleTypeRef ) )
            // InternalMiniJava.g:8250:2: ( ruleTypeRef )
            {
            // InternalMiniJava.g:8250:2: ( ruleTypeRef )
            // InternalMiniJava.g:8251:3: ruleTypeRef
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getTypeRefTypeRefParserRuleCall_3_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleTypeRef();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getTypeRefTypeRefParserRuleCall_3_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__TypeRefAssignment_3"


    // $ANTLR start "rule__Method__NameAssignment_4"
    // InternalMiniJava.g:8260:1: rule__Method__NameAssignment_4 : ( RULE_ID ) ;
    public final void rule__Method__NameAssignment_4() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8264:1: ( ( RULE_ID ) )
            // InternalMiniJava.g:8265:2: ( RULE_ID )
            {
            // InternalMiniJava.g:8265:2: ( RULE_ID )
            // InternalMiniJava.g:8266:3: RULE_ID
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getNameIDTerminalRuleCall_4_0()); 
            }
            match(input,RULE_ID,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getNameIDTerminalRuleCall_4_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__NameAssignment_4"


    // $ANTLR start "rule__Method__ParamsAssignment_6_0"
    // InternalMiniJava.g:8275:1: rule__Method__ParamsAssignment_6_0 : ( ruleParameter ) ;
    public final void rule__Method__ParamsAssignment_6_0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8279:1: ( ( ruleParameter ) )
            // InternalMiniJava.g:8280:2: ( ruleParameter )
            {
            // InternalMiniJava.g:8280:2: ( ruleParameter )
            // InternalMiniJava.g:8281:3: ruleParameter
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getParamsParameterParserRuleCall_6_0_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleParameter();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getParamsParameterParserRuleCall_6_0_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__ParamsAssignment_6_0"


    // $ANTLR start "rule__Method__ParamsAssignment_6_1_1"
    // InternalMiniJava.g:8290:1: rule__Method__ParamsAssignment_6_1_1 : ( ruleParameter ) ;
    public final void rule__Method__ParamsAssignment_6_1_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8294:1: ( ( ruleParameter ) )
            // InternalMiniJava.g:8295:2: ( ruleParameter )
            {
            // InternalMiniJava.g:8295:2: ( ruleParameter )
            // InternalMiniJava.g:8296:3: ruleParameter
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getParamsParameterParserRuleCall_6_1_1_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleParameter();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getParamsParameterParserRuleCall_6_1_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__ParamsAssignment_6_1_1"


    // $ANTLR start "rule__Method__BodyAssignment_8_0"
    // InternalMiniJava.g:8305:1: rule__Method__BodyAssignment_8_0 : ( ruleBlock ) ;
    public final void rule__Method__BodyAssignment_8_0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8309:1: ( ( ruleBlock ) )
            // InternalMiniJava.g:8310:2: ( ruleBlock )
            {
            // InternalMiniJava.g:8310:2: ( ruleBlock )
            // InternalMiniJava.g:8311:3: ruleBlock
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMethodAccess().getBodyBlockParserRuleCall_8_0_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleBlock();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getMethodAccess().getBodyBlockParserRuleCall_8_0_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Method__BodyAssignment_8_0"


    // $ANTLR start "rule__Parameter__TypeRefAssignment_0"
    // InternalMiniJava.g:8320:1: rule__Parameter__TypeRefAssignment_0 : ( ruleTypeRef ) ;
    public final void rule__Parameter__TypeRefAssignment_0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8324:1: ( ( ruleTypeRef ) )
            // InternalMiniJava.g:8325:2: ( ruleTypeRef )
            {
            // InternalMiniJava.g:8325:2: ( ruleTypeRef )
            // InternalMiniJava.g:8326:3: ruleTypeRef
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getParameterAccess().getTypeRefTypeRefParserRuleCall_0_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleTypeRef();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getParameterAccess().getTypeRefTypeRefParserRuleCall_0_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Parameter__TypeRefAssignment_0"


    // $ANTLR start "rule__Parameter__NameAssignment_1"
    // InternalMiniJava.g:8335:1: rule__Parameter__NameAssignment_1 : ( RULE_ID ) ;
    public final void rule__Parameter__NameAssignment_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8339:1: ( ( RULE_ID ) )
            // InternalMiniJava.g:8340:2: ( RULE_ID )
            {
            // InternalMiniJava.g:8340:2: ( RULE_ID )
            // InternalMiniJava.g:8341:3: RULE_ID
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getParameterAccess().getNameIDTerminalRuleCall_1_0()); 
            }
            match(input,RULE_ID,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getParameterAccess().getNameIDTerminalRuleCall_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Parameter__NameAssignment_1"


    // $ANTLR start "rule__Field__AccessAssignment_0"
    // InternalMiniJava.g:8350:1: rule__Field__AccessAssignment_0 : ( ruleAccessLevel ) ;
    public final void rule__Field__AccessAssignment_0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8354:1: ( ( ruleAccessLevel ) )
            // InternalMiniJava.g:8355:2: ( ruleAccessLevel )
            {
            // InternalMiniJava.g:8355:2: ( ruleAccessLevel )
            // InternalMiniJava.g:8356:3: ruleAccessLevel
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getFieldAccess().getAccessAccessLevelEnumRuleCall_0_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleAccessLevel();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getFieldAccess().getAccessAccessLevelEnumRuleCall_0_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Field__AccessAssignment_0"


    // $ANTLR start "rule__Field__TypeRefAssignment_1"
    // InternalMiniJava.g:8365:1: rule__Field__TypeRefAssignment_1 : ( ruleTypeRef ) ;
    public final void rule__Field__TypeRefAssignment_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8369:1: ( ( ruleTypeRef ) )
            // InternalMiniJava.g:8370:2: ( ruleTypeRef )
            {
            // InternalMiniJava.g:8370:2: ( ruleTypeRef )
            // InternalMiniJava.g:8371:3: ruleTypeRef
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getFieldAccess().getTypeRefTypeRefParserRuleCall_1_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleTypeRef();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getFieldAccess().getTypeRefTypeRefParserRuleCall_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Field__TypeRefAssignment_1"


    // $ANTLR start "rule__Field__NameAssignment_2"
    // InternalMiniJava.g:8380:1: rule__Field__NameAssignment_2 : ( RULE_ID ) ;
    public final void rule__Field__NameAssignment_2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8384:1: ( ( RULE_ID ) )
            // InternalMiniJava.g:8385:2: ( RULE_ID )
            {
            // InternalMiniJava.g:8385:2: ( RULE_ID )
            // InternalMiniJava.g:8386:3: RULE_ID
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getFieldAccess().getNameIDTerminalRuleCall_2_0()); 
            }
            match(input,RULE_ID,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getFieldAccess().getNameIDTerminalRuleCall_2_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Field__NameAssignment_2"


    // $ANTLR start "rule__Field__DefaultValueAssignment_3_1"
    // InternalMiniJava.g:8395:1: rule__Field__DefaultValueAssignment_3_1 : ( ruleExpression ) ;
    public final void rule__Field__DefaultValueAssignment_3_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8399:1: ( ( ruleExpression ) )
            // InternalMiniJava.g:8400:2: ( ruleExpression )
            {
            // InternalMiniJava.g:8400:2: ( ruleExpression )
            // InternalMiniJava.g:8401:3: ruleExpression
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getFieldAccess().getDefaultValueExpressionParserRuleCall_3_1_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleExpression();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getFieldAccess().getDefaultValueExpressionParserRuleCall_3_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Field__DefaultValueAssignment_3_1"


    // $ANTLR start "rule__Block__StatementsAssignment_2"
    // InternalMiniJava.g:8410:1: rule__Block__StatementsAssignment_2 : ( ruleStatement ) ;
    public final void rule__Block__StatementsAssignment_2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8414:1: ( ( ruleStatement ) )
            // InternalMiniJava.g:8415:2: ( ruleStatement )
            {
            // InternalMiniJava.g:8415:2: ( ruleStatement )
            // InternalMiniJava.g:8416:3: ruleStatement
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getBlockAccess().getStatementsStatementParserRuleCall_2_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleStatement();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getBlockAccess().getStatementsStatementParserRuleCall_2_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Block__StatementsAssignment_2"


    // $ANTLR start "rule__PrintStatement__ExpressionAssignment_6"
    // InternalMiniJava.g:8425:1: rule__PrintStatement__ExpressionAssignment_6 : ( ruleExpression ) ;
    public final void rule__PrintStatement__ExpressionAssignment_6() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8429:1: ( ( ruleExpression ) )
            // InternalMiniJava.g:8430:2: ( ruleExpression )
            {
            // InternalMiniJava.g:8430:2: ( ruleExpression )
            // InternalMiniJava.g:8431:3: ruleExpression
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrintStatementAccess().getExpressionExpressionParserRuleCall_6_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleExpression();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrintStatementAccess().getExpressionExpressionParserRuleCall_6_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PrintStatement__ExpressionAssignment_6"


    // $ANTLR start "rule__Return__ExpressionAssignment_1"
    // InternalMiniJava.g:8440:1: rule__Return__ExpressionAssignment_1 : ( ruleExpression ) ;
    public final void rule__Return__ExpressionAssignment_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8444:1: ( ( ruleExpression ) )
            // InternalMiniJava.g:8445:2: ( ruleExpression )
            {
            // InternalMiniJava.g:8445:2: ( ruleExpression )
            // InternalMiniJava.g:8446:3: ruleExpression
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getReturnAccess().getExpressionExpressionParserRuleCall_1_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleExpression();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getReturnAccess().getExpressionExpressionParserRuleCall_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Return__ExpressionAssignment_1"


    // $ANTLR start "rule__IfStatement__ExpressionAssignment_2"
    // InternalMiniJava.g:8455:1: rule__IfStatement__ExpressionAssignment_2 : ( ruleExpression ) ;
    public final void rule__IfStatement__ExpressionAssignment_2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8459:1: ( ( ruleExpression ) )
            // InternalMiniJava.g:8460:2: ( ruleExpression )
            {
            // InternalMiniJava.g:8460:2: ( ruleExpression )
            // InternalMiniJava.g:8461:3: ruleExpression
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getIfStatementAccess().getExpressionExpressionParserRuleCall_2_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleExpression();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getIfStatementAccess().getExpressionExpressionParserRuleCall_2_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__IfStatement__ExpressionAssignment_2"


    // $ANTLR start "rule__IfStatement__ThenBlockAssignment_4"
    // InternalMiniJava.g:8470:1: rule__IfStatement__ThenBlockAssignment_4 : ( ruleBlock ) ;
    public final void rule__IfStatement__ThenBlockAssignment_4() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8474:1: ( ( ruleBlock ) )
            // InternalMiniJava.g:8475:2: ( ruleBlock )
            {
            // InternalMiniJava.g:8475:2: ( ruleBlock )
            // InternalMiniJava.g:8476:3: ruleBlock
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getIfStatementAccess().getThenBlockBlockParserRuleCall_4_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleBlock();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getIfStatementAccess().getThenBlockBlockParserRuleCall_4_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__IfStatement__ThenBlockAssignment_4"


    // $ANTLR start "rule__IfStatement__ElseBlockAssignment_5_1"
    // InternalMiniJava.g:8485:1: rule__IfStatement__ElseBlockAssignment_5_1 : ( ruleBlock ) ;
    public final void rule__IfStatement__ElseBlockAssignment_5_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8489:1: ( ( ruleBlock ) )
            // InternalMiniJava.g:8490:2: ( ruleBlock )
            {
            // InternalMiniJava.g:8490:2: ( ruleBlock )
            // InternalMiniJava.g:8491:3: ruleBlock
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getIfStatementAccess().getElseBlockBlockParserRuleCall_5_1_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleBlock();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getIfStatementAccess().getElseBlockBlockParserRuleCall_5_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__IfStatement__ElseBlockAssignment_5_1"


    // $ANTLR start "rule__WhileStatement__ConditionAssignment_2"
    // InternalMiniJava.g:8500:1: rule__WhileStatement__ConditionAssignment_2 : ( ruleExpression ) ;
    public final void rule__WhileStatement__ConditionAssignment_2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8504:1: ( ( ruleExpression ) )
            // InternalMiniJava.g:8505:2: ( ruleExpression )
            {
            // InternalMiniJava.g:8505:2: ( ruleExpression )
            // InternalMiniJava.g:8506:3: ruleExpression
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getWhileStatementAccess().getConditionExpressionParserRuleCall_2_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleExpression();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getWhileStatementAccess().getConditionExpressionParserRuleCall_2_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__WhileStatement__ConditionAssignment_2"


    // $ANTLR start "rule__WhileStatement__BlockAssignment_4"
    // InternalMiniJava.g:8515:1: rule__WhileStatement__BlockAssignment_4 : ( ruleBlock ) ;
    public final void rule__WhileStatement__BlockAssignment_4() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8519:1: ( ( ruleBlock ) )
            // InternalMiniJava.g:8520:2: ( ruleBlock )
            {
            // InternalMiniJava.g:8520:2: ( ruleBlock )
            // InternalMiniJava.g:8521:3: ruleBlock
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getWhileStatementAccess().getBlockBlockParserRuleCall_4_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleBlock();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getWhileStatementAccess().getBlockBlockParserRuleCall_4_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__WhileStatement__BlockAssignment_4"


    // $ANTLR start "rule__ForStatement__DeclarationAssignment_2"
    // InternalMiniJava.g:8530:1: rule__ForStatement__DeclarationAssignment_2 : ( ruleAssignment ) ;
    public final void rule__ForStatement__DeclarationAssignment_2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8534:1: ( ( ruleAssignment ) )
            // InternalMiniJava.g:8535:2: ( ruleAssignment )
            {
            // InternalMiniJava.g:8535:2: ( ruleAssignment )
            // InternalMiniJava.g:8536:3: ruleAssignment
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getForStatementAccess().getDeclarationAssignmentParserRuleCall_2_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleAssignment();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getForStatementAccess().getDeclarationAssignmentParserRuleCall_2_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ForStatement__DeclarationAssignment_2"


    // $ANTLR start "rule__ForStatement__ConditionAssignment_4"
    // InternalMiniJava.g:8545:1: rule__ForStatement__ConditionAssignment_4 : ( ruleExpression ) ;
    public final void rule__ForStatement__ConditionAssignment_4() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8549:1: ( ( ruleExpression ) )
            // InternalMiniJava.g:8550:2: ( ruleExpression )
            {
            // InternalMiniJava.g:8550:2: ( ruleExpression )
            // InternalMiniJava.g:8551:3: ruleExpression
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getForStatementAccess().getConditionExpressionParserRuleCall_4_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleExpression();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getForStatementAccess().getConditionExpressionParserRuleCall_4_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ForStatement__ConditionAssignment_4"


    // $ANTLR start "rule__ForStatement__ProgressionAssignment_6"
    // InternalMiniJava.g:8560:1: rule__ForStatement__ProgressionAssignment_6 : ( ruleAssignment ) ;
    public final void rule__ForStatement__ProgressionAssignment_6() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8564:1: ( ( ruleAssignment ) )
            // InternalMiniJava.g:8565:2: ( ruleAssignment )
            {
            // InternalMiniJava.g:8565:2: ( ruleAssignment )
            // InternalMiniJava.g:8566:3: ruleAssignment
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getForStatementAccess().getProgressionAssignmentParserRuleCall_6_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleAssignment();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getForStatementAccess().getProgressionAssignmentParserRuleCall_6_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ForStatement__ProgressionAssignment_6"


    // $ANTLR start "rule__ForStatement__BlockAssignment_8"
    // InternalMiniJava.g:8575:1: rule__ForStatement__BlockAssignment_8 : ( ruleBlock ) ;
    public final void rule__ForStatement__BlockAssignment_8() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8579:1: ( ( ruleBlock ) )
            // InternalMiniJava.g:8580:2: ( ruleBlock )
            {
            // InternalMiniJava.g:8580:2: ( ruleBlock )
            // InternalMiniJava.g:8581:3: ruleBlock
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getForStatementAccess().getBlockBlockParserRuleCall_8_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleBlock();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getForStatementAccess().getBlockBlockParserRuleCall_8_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ForStatement__BlockAssignment_8"


    // $ANTLR start "rule__ClassRef__ReferencedClassAssignment"
    // InternalMiniJava.g:8590:1: rule__ClassRef__ReferencedClassAssignment : ( ( ruleQualifiedName ) ) ;
    public final void rule__ClassRef__ReferencedClassAssignment() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8594:1: ( ( ( ruleQualifiedName ) ) )
            // InternalMiniJava.g:8595:2: ( ( ruleQualifiedName ) )
            {
            // InternalMiniJava.g:8595:2: ( ( ruleQualifiedName ) )
            // InternalMiniJava.g:8596:3: ( ruleQualifiedName )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassRefAccess().getReferencedClassTypeDeclarationCrossReference_0()); 
            }
            // InternalMiniJava.g:8597:3: ( ruleQualifiedName )
            // InternalMiniJava.g:8598:4: ruleQualifiedName
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getClassRefAccess().getReferencedClassTypeDeclarationQualifiedNameParserRuleCall_0_1()); 
            }
            pushFollow(FOLLOW_2);
            ruleQualifiedName();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassRefAccess().getReferencedClassTypeDeclarationQualifiedNameParserRuleCall_0_1()); 
            }

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getClassRefAccess().getReferencedClassTypeDeclarationCrossReference_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ClassRef__ReferencedClassAssignment"


    // $ANTLR start "rule__VariableDeclaration__TypeRefAssignment_0"
    // InternalMiniJava.g:8609:1: rule__VariableDeclaration__TypeRefAssignment_0 : ( ruleTypeRef ) ;
    public final void rule__VariableDeclaration__TypeRefAssignment_0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8613:1: ( ( ruleTypeRef ) )
            // InternalMiniJava.g:8614:2: ( ruleTypeRef )
            {
            // InternalMiniJava.g:8614:2: ( ruleTypeRef )
            // InternalMiniJava.g:8615:3: ruleTypeRef
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getVariableDeclarationAccess().getTypeRefTypeRefParserRuleCall_0_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleTypeRef();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getVariableDeclarationAccess().getTypeRefTypeRefParserRuleCall_0_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__VariableDeclaration__TypeRefAssignment_0"


    // $ANTLR start "rule__VariableDeclaration__NameAssignment_1"
    // InternalMiniJava.g:8624:1: rule__VariableDeclaration__NameAssignment_1 : ( RULE_ID ) ;
    public final void rule__VariableDeclaration__NameAssignment_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8628:1: ( ( RULE_ID ) )
            // InternalMiniJava.g:8629:2: ( RULE_ID )
            {
            // InternalMiniJava.g:8629:2: ( RULE_ID )
            // InternalMiniJava.g:8630:3: RULE_ID
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getVariableDeclarationAccess().getNameIDTerminalRuleCall_1_0()); 
            }
            match(input,RULE_ID,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getVariableDeclarationAccess().getNameIDTerminalRuleCall_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__VariableDeclaration__NameAssignment_1"


    // $ANTLR start "rule__Assignment__AssigneeAssignment_0"
    // InternalMiniJava.g:8639:1: rule__Assignment__AssigneeAssignment_0 : ( ruleAssignee ) ;
    public final void rule__Assignment__AssigneeAssignment_0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8643:1: ( ( ruleAssignee ) )
            // InternalMiniJava.g:8644:2: ( ruleAssignee )
            {
            // InternalMiniJava.g:8644:2: ( ruleAssignee )
            // InternalMiniJava.g:8645:3: ruleAssignee
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getAssignmentAccess().getAssigneeAssigneeParserRuleCall_0_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleAssignee();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getAssignmentAccess().getAssigneeAssigneeParserRuleCall_0_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Assignment__AssigneeAssignment_0"


    // $ANTLR start "rule__Assignment__ValueAssignment_2"
    // InternalMiniJava.g:8654:1: rule__Assignment__ValueAssignment_2 : ( ruleExpression ) ;
    public final void rule__Assignment__ValueAssignment_2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8658:1: ( ( ruleExpression ) )
            // InternalMiniJava.g:8659:2: ( ruleExpression )
            {
            // InternalMiniJava.g:8659:2: ( ruleExpression )
            // InternalMiniJava.g:8660:3: ruleExpression
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getAssignmentAccess().getValueExpressionParserRuleCall_2_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleExpression();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getAssignmentAccess().getValueExpressionParserRuleCall_2_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Assignment__ValueAssignment_2"


    // $ANTLR start "rule__Or__RightAssignment_1_2"
    // InternalMiniJava.g:8669:1: rule__Or__RightAssignment_1_2 : ( ruleAnd ) ;
    public final void rule__Or__RightAssignment_1_2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8673:1: ( ( ruleAnd ) )
            // InternalMiniJava.g:8674:2: ( ruleAnd )
            {
            // InternalMiniJava.g:8674:2: ( ruleAnd )
            // InternalMiniJava.g:8675:3: ruleAnd
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getOrAccess().getRightAndParserRuleCall_1_2_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleAnd();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getOrAccess().getRightAndParserRuleCall_1_2_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Or__RightAssignment_1_2"


    // $ANTLR start "rule__And__RightAssignment_1_2"
    // InternalMiniJava.g:8684:1: rule__And__RightAssignment_1_2 : ( ruleEquality ) ;
    public final void rule__And__RightAssignment_1_2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8688:1: ( ( ruleEquality ) )
            // InternalMiniJava.g:8689:2: ( ruleEquality )
            {
            // InternalMiniJava.g:8689:2: ( ruleEquality )
            // InternalMiniJava.g:8690:3: ruleEquality
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getAndAccess().getRightEqualityParserRuleCall_1_2_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleEquality();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getAndAccess().getRightEqualityParserRuleCall_1_2_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__And__RightAssignment_1_2"


    // $ANTLR start "rule__Equality__RightAssignment_1_1"
    // InternalMiniJava.g:8699:1: rule__Equality__RightAssignment_1_1 : ( ruleComparison ) ;
    public final void rule__Equality__RightAssignment_1_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8703:1: ( ( ruleComparison ) )
            // InternalMiniJava.g:8704:2: ( ruleComparison )
            {
            // InternalMiniJava.g:8704:2: ( ruleComparison )
            // InternalMiniJava.g:8705:3: ruleComparison
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getEqualityAccess().getRightComparisonParserRuleCall_1_1_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleComparison();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getEqualityAccess().getRightComparisonParserRuleCall_1_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Equality__RightAssignment_1_1"


    // $ANTLR start "rule__Comparison__RightAssignment_1_1"
    // InternalMiniJava.g:8714:1: rule__Comparison__RightAssignment_1_1 : ( rulePlusOrMinus ) ;
    public final void rule__Comparison__RightAssignment_1_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8718:1: ( ( rulePlusOrMinus ) )
            // InternalMiniJava.g:8719:2: ( rulePlusOrMinus )
            {
            // InternalMiniJava.g:8719:2: ( rulePlusOrMinus )
            // InternalMiniJava.g:8720:3: rulePlusOrMinus
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getComparisonAccess().getRightPlusOrMinusParserRuleCall_1_1_0()); 
            }
            pushFollow(FOLLOW_2);
            rulePlusOrMinus();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getComparisonAccess().getRightPlusOrMinusParserRuleCall_1_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Comparison__RightAssignment_1_1"


    // $ANTLR start "rule__PlusOrMinus__RightAssignment_1_1"
    // InternalMiniJava.g:8729:1: rule__PlusOrMinus__RightAssignment_1_1 : ( ruleMulOrDiv ) ;
    public final void rule__PlusOrMinus__RightAssignment_1_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8733:1: ( ( ruleMulOrDiv ) )
            // InternalMiniJava.g:8734:2: ( ruleMulOrDiv )
            {
            // InternalMiniJava.g:8734:2: ( ruleMulOrDiv )
            // InternalMiniJava.g:8735:3: ruleMulOrDiv
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPlusOrMinusAccess().getRightMulOrDivParserRuleCall_1_1_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleMulOrDiv();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getPlusOrMinusAccess().getRightMulOrDivParserRuleCall_1_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__PlusOrMinus__RightAssignment_1_1"


    // $ANTLR start "rule__MulOrDiv__RightAssignment_1_1"
    // InternalMiniJava.g:8744:1: rule__MulOrDiv__RightAssignment_1_1 : ( ruleArrayAccess ) ;
    public final void rule__MulOrDiv__RightAssignment_1_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8748:1: ( ( ruleArrayAccess ) )
            // InternalMiniJava.g:8749:2: ( ruleArrayAccess )
            {
            // InternalMiniJava.g:8749:2: ( ruleArrayAccess )
            // InternalMiniJava.g:8750:3: ruleArrayAccess
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getMulOrDivAccess().getRightArrayAccessParserRuleCall_1_1_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleArrayAccess();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getMulOrDivAccess().getRightArrayAccessParserRuleCall_1_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__MulOrDiv__RightAssignment_1_1"


    // $ANTLR start "rule__ArrayAccess__IndexAssignment_1_2"
    // InternalMiniJava.g:8759:1: rule__ArrayAccess__IndexAssignment_1_2 : ( ruleExpression ) ;
    public final void rule__ArrayAccess__IndexAssignment_1_2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8763:1: ( ( ruleExpression ) )
            // InternalMiniJava.g:8764:2: ( ruleExpression )
            {
            // InternalMiniJava.g:8764:2: ( ruleExpression )
            // InternalMiniJava.g:8765:3: ruleExpression
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getArrayAccessAccess().getIndexExpressionParserRuleCall_1_2_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleExpression();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getArrayAccessAccess().getIndexExpressionParserRuleCall_1_2_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__ArrayAccess__IndexAssignment_1_2"


    // $ANTLR start "rule__Primary__ExpressionAssignment_1_2"
    // InternalMiniJava.g:8774:1: rule__Primary__ExpressionAssignment_1_2 : ( rulePrimary ) ;
    public final void rule__Primary__ExpressionAssignment_1_2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8778:1: ( ( rulePrimary ) )
            // InternalMiniJava.g:8779:2: ( rulePrimary )
            {
            // InternalMiniJava.g:8779:2: ( rulePrimary )
            // InternalMiniJava.g:8780:3: rulePrimary
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrimaryAccess().getExpressionPrimaryParserRuleCall_1_2_0()); 
            }
            pushFollow(FOLLOW_2);
            rulePrimary();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrimaryAccess().getExpressionPrimaryParserRuleCall_1_2_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Primary__ExpressionAssignment_1_2"


    // $ANTLR start "rule__Primary__ExpressionAssignment_2_2"
    // InternalMiniJava.g:8789:1: rule__Primary__ExpressionAssignment_2_2 : ( rulePrimary ) ;
    public final void rule__Primary__ExpressionAssignment_2_2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8793:1: ( ( rulePrimary ) )
            // InternalMiniJava.g:8794:2: ( rulePrimary )
            {
            // InternalMiniJava.g:8794:2: ( rulePrimary )
            // InternalMiniJava.g:8795:3: rulePrimary
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getPrimaryAccess().getExpressionPrimaryParserRuleCall_2_2_0()); 
            }
            pushFollow(FOLLOW_2);
            rulePrimary();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getPrimaryAccess().getExpressionPrimaryParserRuleCall_2_2_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__Primary__ExpressionAssignment_2_2"


    // $ANTLR start "rule__SelectionExpression__FieldAssignment_1_0_2"
    // InternalMiniJava.g:8804:1: rule__SelectionExpression__FieldAssignment_1_0_2 : ( ( RULE_ID ) ) ;
    public final void rule__SelectionExpression__FieldAssignment_1_0_2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8808:1: ( ( ( RULE_ID ) ) )
            // InternalMiniJava.g:8809:2: ( ( RULE_ID ) )
            {
            // InternalMiniJava.g:8809:2: ( ( RULE_ID ) )
            // InternalMiniJava.g:8810:3: ( RULE_ID )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionAccess().getFieldFieldCrossReference_1_0_2_0()); 
            }
            // InternalMiniJava.g:8811:3: ( RULE_ID )
            // InternalMiniJava.g:8812:4: RULE_ID
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionAccess().getFieldFieldIDTerminalRuleCall_1_0_2_0_1()); 
            }
            match(input,RULE_ID,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionAccess().getFieldFieldIDTerminalRuleCall_1_0_2_0_1()); 
            }

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionAccess().getFieldFieldCrossReference_1_0_2_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__FieldAssignment_1_0_2"


    // $ANTLR start "rule__SelectionExpression__MethodAssignment_1_1_2"
    // InternalMiniJava.g:8823:1: rule__SelectionExpression__MethodAssignment_1_1_2 : ( ( RULE_ID ) ) ;
    public final void rule__SelectionExpression__MethodAssignment_1_1_2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8827:1: ( ( ( RULE_ID ) ) )
            // InternalMiniJava.g:8828:2: ( ( RULE_ID ) )
            {
            // InternalMiniJava.g:8828:2: ( ( RULE_ID ) )
            // InternalMiniJava.g:8829:3: ( RULE_ID )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionAccess().getMethodMethodCrossReference_1_1_2_0()); 
            }
            // InternalMiniJava.g:8830:3: ( RULE_ID )
            // InternalMiniJava.g:8831:4: RULE_ID
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionAccess().getMethodMethodIDTerminalRuleCall_1_1_2_0_1()); 
            }
            match(input,RULE_ID,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionAccess().getMethodMethodIDTerminalRuleCall_1_1_2_0_1()); 
            }

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionAccess().getMethodMethodCrossReference_1_1_2_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__MethodAssignment_1_1_2"


    // $ANTLR start "rule__SelectionExpression__ArgsAssignment_1_1_4_0"
    // InternalMiniJava.g:8842:1: rule__SelectionExpression__ArgsAssignment_1_1_4_0 : ( ruleExpression ) ;
    public final void rule__SelectionExpression__ArgsAssignment_1_1_4_0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8846:1: ( ( ruleExpression ) )
            // InternalMiniJava.g:8847:2: ( ruleExpression )
            {
            // InternalMiniJava.g:8847:2: ( ruleExpression )
            // InternalMiniJava.g:8848:3: ruleExpression
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionAccess().getArgsExpressionParserRuleCall_1_1_4_0_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleExpression();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionAccess().getArgsExpressionParserRuleCall_1_1_4_0_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__ArgsAssignment_1_1_4_0"


    // $ANTLR start "rule__SelectionExpression__ArgsAssignment_1_1_4_1_1"
    // InternalMiniJava.g:8857:1: rule__SelectionExpression__ArgsAssignment_1_1_4_1_1 : ( ruleExpression ) ;
    public final void rule__SelectionExpression__ArgsAssignment_1_1_4_1_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8861:1: ( ( ruleExpression ) )
            // InternalMiniJava.g:8862:2: ( ruleExpression )
            {
            // InternalMiniJava.g:8862:2: ( ruleExpression )
            // InternalMiniJava.g:8863:3: ruleExpression
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getSelectionExpressionAccess().getArgsExpressionParserRuleCall_1_1_4_1_1_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleExpression();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getSelectionExpressionAccess().getArgsExpressionParserRuleCall_1_1_4_1_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__SelectionExpression__ArgsAssignment_1_1_4_1_1"


    // $ANTLR start "rule__TerminalExpression__ValueAssignment_0_1"
    // InternalMiniJava.g:8872:1: rule__TerminalExpression__ValueAssignment_0_1 : ( RULE_STRING ) ;
    public final void rule__TerminalExpression__ValueAssignment_0_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8876:1: ( ( RULE_STRING ) )
            // InternalMiniJava.g:8877:2: ( RULE_STRING )
            {
            // InternalMiniJava.g:8877:2: ( RULE_STRING )
            // InternalMiniJava.g:8878:3: RULE_STRING
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getValueSTRINGTerminalRuleCall_0_1_0()); 
            }
            match(input,RULE_STRING,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getValueSTRINGTerminalRuleCall_0_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__ValueAssignment_0_1"


    // $ANTLR start "rule__TerminalExpression__ValueAssignment_1_1"
    // InternalMiniJava.g:8887:1: rule__TerminalExpression__ValueAssignment_1_1 : ( RULE_INT ) ;
    public final void rule__TerminalExpression__ValueAssignment_1_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8891:1: ( ( RULE_INT ) )
            // InternalMiniJava.g:8892:2: ( RULE_INT )
            {
            // InternalMiniJava.g:8892:2: ( RULE_INT )
            // InternalMiniJava.g:8893:3: RULE_INT
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getValueINTTerminalRuleCall_1_1_0()); 
            }
            match(input,RULE_INT,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getValueINTTerminalRuleCall_1_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__ValueAssignment_1_1"


    // $ANTLR start "rule__TerminalExpression__ValueAssignment_2_1"
    // InternalMiniJava.g:8902:1: rule__TerminalExpression__ValueAssignment_2_1 : ( ( rule__TerminalExpression__ValueAlternatives_2_1_0 ) ) ;
    public final void rule__TerminalExpression__ValueAssignment_2_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8906:1: ( ( ( rule__TerminalExpression__ValueAlternatives_2_1_0 ) ) )
            // InternalMiniJava.g:8907:2: ( ( rule__TerminalExpression__ValueAlternatives_2_1_0 ) )
            {
            // InternalMiniJava.g:8907:2: ( ( rule__TerminalExpression__ValueAlternatives_2_1_0 ) )
            // InternalMiniJava.g:8908:3: ( rule__TerminalExpression__ValueAlternatives_2_1_0 )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getValueAlternatives_2_1_0()); 
            }
            // InternalMiniJava.g:8909:3: ( rule__TerminalExpression__ValueAlternatives_2_1_0 )
            // InternalMiniJava.g:8909:4: rule__TerminalExpression__ValueAlternatives_2_1_0
            {
            pushFollow(FOLLOW_2);
            rule__TerminalExpression__ValueAlternatives_2_1_0();

            state._fsp--;
            if (state.failed) return ;

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getValueAlternatives_2_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__ValueAssignment_2_1"


    // $ANTLR start "rule__TerminalExpression__TypeAssignment_6_2"
    // InternalMiniJava.g:8917:1: rule__TerminalExpression__TypeAssignment_6_2 : ( ( RULE_ID ) ) ;
    public final void rule__TerminalExpression__TypeAssignment_6_2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8921:1: ( ( ( RULE_ID ) ) )
            // InternalMiniJava.g:8922:2: ( ( RULE_ID ) )
            {
            // InternalMiniJava.g:8922:2: ( ( RULE_ID ) )
            // InternalMiniJava.g:8923:3: ( RULE_ID )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getTypeClassCrossReference_6_2_0()); 
            }
            // InternalMiniJava.g:8924:3: ( RULE_ID )
            // InternalMiniJava.g:8925:4: RULE_ID
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getTypeClassIDTerminalRuleCall_6_2_0_1()); 
            }
            match(input,RULE_ID,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getTypeClassIDTerminalRuleCall_6_2_0_1()); 
            }

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getTypeClassCrossReference_6_2_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__TypeAssignment_6_2"


    // $ANTLR start "rule__TerminalExpression__ArgsAssignment_6_4_0"
    // InternalMiniJava.g:8936:1: rule__TerminalExpression__ArgsAssignment_6_4_0 : ( ruleExpression ) ;
    public final void rule__TerminalExpression__ArgsAssignment_6_4_0() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8940:1: ( ( ruleExpression ) )
            // InternalMiniJava.g:8941:2: ( ruleExpression )
            {
            // InternalMiniJava.g:8941:2: ( ruleExpression )
            // InternalMiniJava.g:8942:3: ruleExpression
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getArgsExpressionParserRuleCall_6_4_0_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleExpression();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getArgsExpressionParserRuleCall_6_4_0_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__ArgsAssignment_6_4_0"


    // $ANTLR start "rule__TerminalExpression__ArgsAssignment_6_4_1_1"
    // InternalMiniJava.g:8951:1: rule__TerminalExpression__ArgsAssignment_6_4_1_1 : ( ruleExpression ) ;
    public final void rule__TerminalExpression__ArgsAssignment_6_4_1_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8955:1: ( ( ruleExpression ) )
            // InternalMiniJava.g:8956:2: ( ruleExpression )
            {
            // InternalMiniJava.g:8956:2: ( ruleExpression )
            // InternalMiniJava.g:8957:3: ruleExpression
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getArgsExpressionParserRuleCall_6_4_1_1_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleExpression();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getArgsExpressionParserRuleCall_6_4_1_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__ArgsAssignment_6_4_1_1"


    // $ANTLR start "rule__TerminalExpression__TypeAssignment_7_2"
    // InternalMiniJava.g:8966:1: rule__TerminalExpression__TypeAssignment_7_2 : ( ruleTypeRef ) ;
    public final void rule__TerminalExpression__TypeAssignment_7_2() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8970:1: ( ( ruleTypeRef ) )
            // InternalMiniJava.g:8971:2: ( ruleTypeRef )
            {
            // InternalMiniJava.g:8971:2: ( ruleTypeRef )
            // InternalMiniJava.g:8972:3: ruleTypeRef
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getTypeTypeRefParserRuleCall_7_2_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleTypeRef();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getTypeTypeRefParserRuleCall_7_2_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__TypeAssignment_7_2"


    // $ANTLR start "rule__TerminalExpression__SizeAssignment_7_4"
    // InternalMiniJava.g:8981:1: rule__TerminalExpression__SizeAssignment_7_4 : ( ruleExpression ) ;
    public final void rule__TerminalExpression__SizeAssignment_7_4() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:8985:1: ( ( ruleExpression ) )
            // InternalMiniJava.g:8986:2: ( ruleExpression )
            {
            // InternalMiniJava.g:8986:2: ( ruleExpression )
            // InternalMiniJava.g:8987:3: ruleExpression
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getSizeExpressionParserRuleCall_7_4_0()); 
            }
            pushFollow(FOLLOW_2);
            ruleExpression();

            state._fsp--;
            if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getSizeExpressionParserRuleCall_7_4_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__SizeAssignment_7_4"


    // $ANTLR start "rule__TerminalExpression__SymbolAssignment_8_1"
    // InternalMiniJava.g:8996:1: rule__TerminalExpression__SymbolAssignment_8_1 : ( ( RULE_ID ) ) ;
    public final void rule__TerminalExpression__SymbolAssignment_8_1() throws RecognitionException {

        		int stackSize = keepStackSize();
        	
        try {
            // InternalMiniJava.g:9000:1: ( ( ( RULE_ID ) ) )
            // InternalMiniJava.g:9001:2: ( ( RULE_ID ) )
            {
            // InternalMiniJava.g:9001:2: ( ( RULE_ID ) )
            // InternalMiniJava.g:9002:3: ( RULE_ID )
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getSymbolSymbolCrossReference_8_1_0()); 
            }
            // InternalMiniJava.g:9003:3: ( RULE_ID )
            // InternalMiniJava.g:9004:4: RULE_ID
            {
            if ( state.backtracking==0 ) {
               before(grammarAccess.getTerminalExpressionAccess().getSymbolSymbolIDTerminalRuleCall_8_1_0_1()); 
            }
            match(input,RULE_ID,FOLLOW_2); if (state.failed) return ;
            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getSymbolSymbolIDTerminalRuleCall_8_1_0_1()); 
            }

            }

            if ( state.backtracking==0 ) {
               after(grammarAccess.getTerminalExpressionAccess().getSymbolSymbolCrossReference_8_1_0()); 
            }

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {

            	restoreStackSize(stackSize);

        }
        return ;
    }
    // $ANTLR end "rule__TerminalExpression__SymbolAssignment_8_1"

    // $ANTLR start synpred5_InternalMiniJava
    public final void synpred5_InternalMiniJava_fragment() throws RecognitionException {   
        // InternalMiniJava.g:1093:2: ( ( ( rule__Statement__Group_1__0 ) ) )
        // InternalMiniJava.g:1093:2: ( ( rule__Statement__Group_1__0 ) )
        {
        // InternalMiniJava.g:1093:2: ( ( rule__Statement__Group_1__0 ) )
        // InternalMiniJava.g:1094:3: ( rule__Statement__Group_1__0 )
        {
        if ( state.backtracking==0 ) {
           before(grammarAccess.getStatementAccess().getGroup_1()); 
        }
        // InternalMiniJava.g:1095:3: ( rule__Statement__Group_1__0 )
        // InternalMiniJava.g:1095:4: rule__Statement__Group_1__0
        {
        pushFollow(FOLLOW_2);
        rule__Statement__Group_1__0();

        state._fsp--;
        if (state.failed) return ;

        }


        }


        }
    }
    // $ANTLR end synpred5_InternalMiniJava

    // $ANTLR start synpred16_InternalMiniJava
    public final void synpred16_InternalMiniJava_fragment() throws RecognitionException {   
        // InternalMiniJava.g:1204:2: ( ( ( ruleParameter ) ) )
        // InternalMiniJava.g:1204:2: ( ( ruleParameter ) )
        {
        // InternalMiniJava.g:1204:2: ( ( ruleParameter ) )
        // InternalMiniJava.g:1205:3: ( ruleParameter )
        {
        if ( state.backtracking==0 ) {
           before(grammarAccess.getSymbolAccess().getParameterParserRuleCall_0()); 
        }
        // InternalMiniJava.g:1206:3: ( ruleParameter )
        // InternalMiniJava.g:1206:4: ruleParameter
        {
        pushFollow(FOLLOW_2);
        ruleParameter();

        state._fsp--;
        if (state.failed) return ;

        }


        }


        }
    }
    // $ANTLR end synpred16_InternalMiniJava

    // Delegated rules

    public final boolean synpred5_InternalMiniJava() {
        state.backtracking++;
        int start = input.mark();
        try {
            synpred5_InternalMiniJava_fragment(); // can never throw exception
        } catch (RecognitionException re) {
            System.err.println("impossible: "+re);
        }
        boolean success = !state.failed;
        input.rewind(start);
        state.backtracking--;
        state.failed=false;
        return success;
    }
    public final boolean synpred16_InternalMiniJava() {
        state.backtracking++;
        int start = input.mark();
        try {
            synpred16_InternalMiniJava_fragment(); // can never throw exception
        } catch (RecognitionException re) {
            System.err.println("impossible: "+re);
        }
        boolean success = !state.failed;
        input.rewind(start);
        state.backtracking--;
        state.failed=false;
        return success;
    }


    protected DFA2 dfa2 = new DFA2(this);
    protected DFA4 dfa4 = new DFA4(this);
    protected DFA6 dfa6 = new DFA6(this);
    protected DFA7 dfa7 = new DFA7(this);
    protected DFA8 dfa8 = new DFA8(this);
    protected DFA15 dfa15 = new DFA15(this);
    static final String dfa_1s = "\20\uffff";
    static final String dfa_2s = "\11\4\1\uffff\1\4\1\50\1\13\2\4\1\uffff";
    static final String dfa_3s = "\4\100\5\47\1\uffff\1\4\1\50\1\36\1\47\1\34\1\uffff";
    static final String dfa_4s = "\11\uffff\1\2\5\uffff\1\1";
    static final String dfa_5s = "\20\uffff}>";
    static final String[] dfa_6s = {
            "\1\4\11\uffff\1\1\1\2\1\3\30\uffff\1\5\1\6\1\7\1\10\22\uffff\2\11",
            "\1\4\44\uffff\1\5\1\6\1\7\1\10\22\uffff\2\11",
            "\1\4\44\uffff\1\5\1\6\1\7\1\10\22\uffff\2\11",
            "\1\4\44\uffff\1\5\1\6\1\7\1\10\22\uffff\2\11",
            "\1\14\16\uffff\1\12\10\uffff\1\11\12\uffff\1\13",
            "\1\14\27\uffff\1\11\12\uffff\1\13",
            "\1\14\27\uffff\1\11\12\uffff\1\13",
            "\1\14\27\uffff\1\11\12\uffff\1\13",
            "\1\14\27\uffff\1\11\12\uffff\1\13",
            "",
            "\1\15",
            "\1\16",
            "\1\17\20\uffff\1\11\1\uffff\1\17",
            "\1\14\16\uffff\1\12\10\uffff\1\11\12\uffff\1\13",
            "\1\14\27\uffff\1\11",
            ""
    };

    static final short[] dfa_1 = DFA.unpackEncodedString(dfa_1s);
    static final char[] dfa_2 = DFA.unpackEncodedStringToUnsignedChars(dfa_2s);
    static final char[] dfa_3 = DFA.unpackEncodedStringToUnsignedChars(dfa_3s);
    static final short[] dfa_4 = DFA.unpackEncodedString(dfa_4s);
    static final short[] dfa_5 = DFA.unpackEncodedString(dfa_5s);
    static final short[][] dfa_6 = unpackEncodedStringArray(dfa_6s);

    class DFA2 extends DFA {

        public DFA2(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 2;
            this.eot = dfa_1;
            this.eof = dfa_1;
            this.min = dfa_2;
            this.max = dfa_3;
            this.accept = dfa_4;
            this.special = dfa_5;
            this.transition = dfa_6;
        }
        public String getDescription() {
            return "1040:1: rule__Member__Alternatives : ( ( ruleField ) | ( ruleMethod ) );";
        }
    }
    static final String dfa_7s = "\30\uffff";
    static final String dfa_8s = "\1\4\4\uffff\11\0\12\uffff";
    static final String dfa_9s = "\1\76\4\uffff\11\0\12\uffff";
    static final String dfa_10s = "\1\uffff\1\1\1\2\17\uffff\1\3\1\4\1\5\1\6\1\7\1\10";
    static final String dfa_11s = "\5\uffff\1\0\1\1\1\2\1\3\1\4\1\5\1\6\1\7\1\10\12\uffff}>";
    static final String[] dfa_12s = {
            "\1\15\1\5\1\6\5\uffff\1\7\1\10\10\uffff\1\26\5\uffff\1\2\2\uffff\1\25\2\uffff\1\1\1\22\1\uffff\1\23\1\24\2\uffff\4\2\11\uffff\1\2\3\uffff\1\2\1\11\1\12\1\13\1\14",
            "",
            "",
            "",
            "",
            "\1\uffff",
            "\1\uffff",
            "\1\uffff",
            "\1\uffff",
            "\1\uffff",
            "\1\uffff",
            "\1\uffff",
            "\1\uffff",
            "\1\uffff",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            ""
    };

    static final short[] dfa_7 = DFA.unpackEncodedString(dfa_7s);
    static final char[] dfa_8 = DFA.unpackEncodedStringToUnsignedChars(dfa_8s);
    static final char[] dfa_9 = DFA.unpackEncodedStringToUnsignedChars(dfa_9s);
    static final short[] dfa_10 = DFA.unpackEncodedString(dfa_10s);
    static final short[] dfa_11 = DFA.unpackEncodedString(dfa_11s);
    static final short[][] dfa_12 = unpackEncodedStringArray(dfa_12s);

    class DFA4 extends DFA {

        public DFA4(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 4;
            this.eot = dfa_7;
            this.eof = dfa_7;
            this.min = dfa_8;
            this.max = dfa_9;
            this.accept = dfa_10;
            this.special = dfa_11;
            this.transition = dfa_12;
        }
        public String getDescription() {
            return "1082:1: rule__Statement__Alternatives : ( ( ( rule__Statement__Group_0__0 ) ) | ( ( rule__Statement__Group_1__0 ) ) | ( ruleIfStatement ) | ( ruleWhileStatement ) | ( ruleForStatement ) | ( ( rule__Statement__Group_5__0 ) ) | ( ruleBlock ) | ( ( rule__Statement__Group_7__0 ) ) );";
        }
        public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
            TokenStream input = (TokenStream)_input;
        	int _s = s;
            switch ( s ) {
                    case 0 : 
                        int LA4_5 = input.LA(1);

                         
                        int index4_5 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred5_InternalMiniJava()) ) {s = 2;}

                        else if ( (true) ) {s = 23;}

                         
                        input.seek(index4_5);
                        if ( s>=0 ) return s;
                        break;
                    case 1 : 
                        int LA4_6 = input.LA(1);

                         
                        int index4_6 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred5_InternalMiniJava()) ) {s = 2;}

                        else if ( (true) ) {s = 23;}

                         
                        input.seek(index4_6);
                        if ( s>=0 ) return s;
                        break;
                    case 2 : 
                        int LA4_7 = input.LA(1);

                         
                        int index4_7 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred5_InternalMiniJava()) ) {s = 2;}

                        else if ( (true) ) {s = 23;}

                         
                        input.seek(index4_7);
                        if ( s>=0 ) return s;
                        break;
                    case 3 : 
                        int LA4_8 = input.LA(1);

                         
                        int index4_8 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred5_InternalMiniJava()) ) {s = 2;}

                        else if ( (true) ) {s = 23;}

                         
                        input.seek(index4_8);
                        if ( s>=0 ) return s;
                        break;
                    case 4 : 
                        int LA4_9 = input.LA(1);

                         
                        int index4_9 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred5_InternalMiniJava()) ) {s = 2;}

                        else if ( (true) ) {s = 23;}

                         
                        input.seek(index4_9);
                        if ( s>=0 ) return s;
                        break;
                    case 5 : 
                        int LA4_10 = input.LA(1);

                         
                        int index4_10 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred5_InternalMiniJava()) ) {s = 2;}

                        else if ( (true) ) {s = 23;}

                         
                        input.seek(index4_10);
                        if ( s>=0 ) return s;
                        break;
                    case 6 : 
                        int LA4_11 = input.LA(1);

                         
                        int index4_11 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred5_InternalMiniJava()) ) {s = 2;}

                        else if ( (true) ) {s = 23;}

                         
                        input.seek(index4_11);
                        if ( s>=0 ) return s;
                        break;
                    case 7 : 
                        int LA4_12 = input.LA(1);

                         
                        int index4_12 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred5_InternalMiniJava()) ) {s = 2;}

                        else if ( (true) ) {s = 23;}

                         
                        input.seek(index4_12);
                        if ( s>=0 ) return s;
                        break;
                    case 8 : 
                        int LA4_13 = input.LA(1);

                         
                        int index4_13 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred5_InternalMiniJava()) ) {s = 2;}

                        else if ( (true) ) {s = 23;}

                         
                        input.seek(index4_13);
                        if ( s>=0 ) return s;
                        break;
            }
            if (state.backtracking>0) {state.failed=true; return -1;}
            NoViableAltException nvae =
                new NoViableAltException(getDescription(), 4, _s, input);
            error(nvae);
            throw nvae;
        }
    }
    static final String dfa_13s = "\15\uffff";
    static final String dfa_14s = "\11\uffff\1\14\3\uffff";
    static final String dfa_15s = "\6\4\1\uffff\1\4\1\50\1\13\2\4\1\uffff";
    static final String dfa_16s = "\1\100\5\47\1\uffff\1\4\1\50\1\36\1\47\1\34\1\uffff";
    static final String dfa_17s = "\6\uffff\1\2\5\uffff\1\1";
    static final String dfa_18s = "\15\uffff}>";
    static final String[] dfa_19s = {
            "\1\1\11\uffff\3\6\30\uffff\1\2\1\3\1\4\1\5\22\uffff\2\6",
            "\1\11\16\uffff\1\7\10\uffff\1\6\12\uffff\1\10",
            "\1\11\27\uffff\1\6\12\uffff\1\10",
            "\1\11\27\uffff\1\6\12\uffff\1\10",
            "\1\11\27\uffff\1\6\12\uffff\1\10",
            "\1\11\27\uffff\1\6\12\uffff\1\10",
            "",
            "\1\12",
            "\1\13",
            "\1\6\20\uffff\1\6\1\uffff\1\6",
            "\1\11\16\uffff\1\7\10\uffff\1\6\12\uffff\1\10",
            "\1\11\27\uffff\1\6",
            ""
    };

    static final short[] dfa_13 = DFA.unpackEncodedString(dfa_13s);
    static final short[] dfa_14 = DFA.unpackEncodedString(dfa_14s);
    static final char[] dfa_15 = DFA.unpackEncodedStringToUnsignedChars(dfa_15s);
    static final char[] dfa_16 = DFA.unpackEncodedStringToUnsignedChars(dfa_16s);
    static final short[] dfa_17 = DFA.unpackEncodedString(dfa_17s);
    static final short[] dfa_18 = DFA.unpackEncodedString(dfa_18s);
    static final short[][] dfa_19 = unpackEncodedStringArray(dfa_19s);

    class DFA6 extends DFA {

        public DFA6(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 6;
            this.eot = dfa_13;
            this.eof = dfa_14;
            this.min = dfa_15;
            this.max = dfa_16;
            this.accept = dfa_17;
            this.special = dfa_18;
            this.transition = dfa_19;
        }
        public String getDescription() {
            return "1178:1: rule__TypedDeclaration__Alternatives : ( ( ruleSymbol ) | ( ruleMember ) );";
        }
    }
    static final String dfa_20s = "\7\4\1\50\1\0\2\4\2\uffff";
    static final String dfa_21s = "\1\54\5\47\1\4\1\50\1\0\1\47\1\4\2\uffff";
    static final String dfa_22s = "\13\uffff\1\1\1\2";
    static final String dfa_23s = "\10\uffff\1\0\4\uffff}>";
    static final String[] dfa_24s = {
            "\1\1\44\uffff\1\2\1\3\1\4\1\5",
            "\1\10\16\uffff\1\6\23\uffff\1\7",
            "\1\10\42\uffff\1\7",
            "\1\10\42\uffff\1\7",
            "\1\10\42\uffff\1\7",
            "\1\10\42\uffff\1\7",
            "\1\11",
            "\1\12",
            "\1\uffff",
            "\1\10\16\uffff\1\6\23\uffff\1\7",
            "\1\10",
            "",
            ""
    };
    static final char[] dfa_20 = DFA.unpackEncodedStringToUnsignedChars(dfa_20s);
    static final char[] dfa_21 = DFA.unpackEncodedStringToUnsignedChars(dfa_21s);
    static final short[] dfa_22 = DFA.unpackEncodedString(dfa_22s);
    static final short[] dfa_23 = DFA.unpackEncodedString(dfa_23s);
    static final short[][] dfa_24 = unpackEncodedStringArray(dfa_24s);

    class DFA7 extends DFA {

        public DFA7(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 7;
            this.eot = dfa_13;
            this.eof = dfa_13;
            this.min = dfa_20;
            this.max = dfa_21;
            this.accept = dfa_22;
            this.special = dfa_23;
            this.transition = dfa_24;
        }
        public String getDescription() {
            return "1199:1: rule__Symbol__Alternatives : ( ( ( ruleParameter ) ) | ( ruleVariableDeclaration ) );";
        }
        public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
            TokenStream input = (TokenStream)_input;
        	int _s = s;
            switch ( s ) {
                    case 0 : 
                        int LA7_8 = input.LA(1);

                         
                        int index7_8 = input.index();
                        input.rewind();
                        s = -1;
                        if ( (synpred16_InternalMiniJava()) ) {s = 11;}

                        else if ( (true) ) {s = 12;}

                         
                        input.seek(index7_8);
                        if ( s>=0 ) return s;
                        break;
            }
            if (state.backtracking>0) {state.failed=true; return -1;}
            NoViableAltException nvae =
                new NoViableAltException(getDescription(), 7, _s, input);
            error(nvae);
            throw nvae;
        }
    }
    static final String dfa_25s = "\7\uffff";
    static final String dfa_26s = "\2\uffff\1\1\3\uffff\1\1";
    static final String dfa_27s = "\1\4\1\uffff\1\4\1\uffff\3\4";
    static final String dfa_28s = "\1\76\1\uffff\1\47\1\uffff\1\71\1\76\1\47";
    static final String dfa_29s = "\1\uffff\1\1\1\uffff\1\2\3\uffff";
    static final String dfa_30s = "\7\uffff}>";
    static final String[] dfa_31s = {
            "\1\2\2\1\5\uffff\2\1\16\uffff\1\1\14\uffff\4\3\11\uffff\1\1\3\uffff\5\1",
            "",
            "\1\3\16\uffff\1\4\12\uffff\1\1\10\uffff\1\5",
            "",
            "\1\6\64\uffff\1\1",
            "\3\1\5\uffff\2\1\16\uffff\1\1\13\uffff\1\3\15\uffff\1\1\3\uffff\5\1",
            "\1\3\16\uffff\1\4\10\uffff\1\1\1\uffff\1\1\10\uffff\1\5"
    };

    static final short[] dfa_25 = DFA.unpackEncodedString(dfa_25s);
    static final short[] dfa_26 = DFA.unpackEncodedString(dfa_26s);
    static final char[] dfa_27 = DFA.unpackEncodedStringToUnsignedChars(dfa_27s);
    static final char[] dfa_28 = DFA.unpackEncodedStringToUnsignedChars(dfa_28s);
    static final short[] dfa_29 = DFA.unpackEncodedString(dfa_29s);
    static final short[] dfa_30 = DFA.unpackEncodedString(dfa_30s);
    static final short[][] dfa_31 = unpackEncodedStringArray(dfa_31s);

    class DFA8 extends DFA {

        public DFA8(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 8;
            this.eot = dfa_25;
            this.eof = dfa_26;
            this.min = dfa_27;
            this.max = dfa_28;
            this.accept = dfa_29;
            this.special = dfa_30;
            this.transition = dfa_31;
        }
        public String getDescription() {
            return "1220:1: rule__Assignee__Alternatives : ( ( ( ruleArrayAccess ) ) | ( ruleVariableDeclaration ) );";
        }
    }
    static final String dfa_32s = "\14\uffff";
    static final String dfa_33s = "\1\4\6\uffff\1\4\1\uffff\1\23\2\uffff";
    static final String dfa_34s = "\1\76\6\uffff\1\54\1\uffff\1\47\2\uffff";
    static final String dfa_35s = "\1\uffff\1\1\1\2\1\3\1\4\1\5\1\6\1\uffff\1\11\1\uffff\1\10\1\7";
    static final String dfa_36s = "\14\uffff}>";
    static final String[] dfa_37s = {
            "\1\10\1\1\1\2\5\uffff\2\3\55\uffff\1\4\1\5\1\6\1\7",
            "",
            "",
            "",
            "",
            "",
            "",
            "\1\11\44\uffff\4\12",
            "",
            "\1\12\10\uffff\1\13\12\uffff\1\12",
            "",
            ""
    };

    static final short[] dfa_32 = DFA.unpackEncodedString(dfa_32s);
    static final char[] dfa_33 = DFA.unpackEncodedStringToUnsignedChars(dfa_33s);
    static final char[] dfa_34 = DFA.unpackEncodedStringToUnsignedChars(dfa_34s);
    static final short[] dfa_35 = DFA.unpackEncodedString(dfa_35s);
    static final short[] dfa_36 = DFA.unpackEncodedString(dfa_36s);
    static final short[][] dfa_37 = unpackEncodedStringArray(dfa_37s);

    class DFA15 extends DFA {

        public DFA15(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 15;
            this.eot = dfa_32;
            this.eof = dfa_32;
            this.min = dfa_33;
            this.max = dfa_34;
            this.accept = dfa_35;
            this.special = dfa_36;
            this.transition = dfa_37;
        }
        public String getDescription() {
            return "1391:1: rule__TerminalExpression__Alternatives : ( ( ( rule__TerminalExpression__Group_0__0 ) ) | ( ( rule__TerminalExpression__Group_1__0 ) ) | ( ( rule__TerminalExpression__Group_2__0 ) ) | ( ( rule__TerminalExpression__Group_3__0 ) ) | ( ( rule__TerminalExpression__Group_4__0 ) ) | ( ( rule__TerminalExpression__Group_5__0 ) ) | ( ( rule__TerminalExpression__Group_6__0 ) ) | ( ( rule__TerminalExpression__Group_7__0 ) ) | ( ( rule__TerminalExpression__Group_8__0 ) ) );";
        }
    }
 

    public static final BitSet FOLLOW_1 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_2 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_3 = new BitSet(new long[]{0x800000000825C000L});
    public static final BitSet FOLLOW_4 = new BitSet(new long[]{0x0000000000040002L});
    public static final BitSet FOLLOW_5 = new BitSet(new long[]{0x800000000821C002L});
    public static final BitSet FOLLOW_6 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_7 = new BitSet(new long[]{0x0000000000000800L});
    public static final BitSet FOLLOW_8 = new BitSet(new long[]{0x0000000000080000L});
    public static final BitSet FOLLOW_9 = new BitSet(new long[]{0x0000000000080002L});
    public static final BitSet FOLLOW_10 = new BitSet(new long[]{0x0000000000100000L});
    public static final BitSet FOLLOW_11 = new BitSet(new long[]{0x800000000021C000L});
    public static final BitSet FOLLOW_12 = new BitSet(new long[]{0x0000000003400000L});
    public static final BitSet FOLLOW_13 = new BitSet(new long[]{0x80001E000081C010L,0x0000000000000001L});
    public static final BitSet FOLLOW_14 = new BitSet(new long[]{0x80001E000001C012L,0x0000000000000001L});
    public static final BitSet FOLLOW_15 = new BitSet(new long[]{0x0000000004000000L});
    public static final BitSet FOLLOW_16 = new BitSet(new long[]{0x0000000004000002L});
    public static final BitSet FOLLOW_17 = new BitSet(new long[]{0x800000000821C000L});
    public static final BitSet FOLLOW_18 = new BitSet(new long[]{0x0000000001400000L});
    public static final BitSet FOLLOW_19 = new BitSet(new long[]{0x80001E000001C010L,0x0000000000000001L});
    public static final BitSet FOLLOW_20 = new BitSet(new long[]{0x0000000010000010L});
    public static final BitSet FOLLOW_21 = new BitSet(new long[]{0x00001E002001C010L});
    public static final BitSet FOLLOW_22 = new BitSet(new long[]{0x0000000000400800L});
    public static final BitSet FOLLOW_23 = new BitSet(new long[]{0x00001E000001C010L});
    public static final BitSet FOLLOW_24 = new BitSet(new long[]{0x0000000040000800L});
    public static final BitSet FOLLOW_25 = new BitSet(new long[]{0x7C40000010003070L});
    public static final BitSet FOLLOW_26 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_27 = new BitSet(new long[]{0x7C401E6C90C1F070L});
    public static final BitSet FOLLOW_28 = new BitSet(new long[]{0x7C401E6C9041F072L});
    public static final BitSet FOLLOW_29 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_30 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_31 = new BitSet(new long[]{0x0000000010000000L});
    public static final BitSet FOLLOW_32 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_33 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_34 = new BitSet(new long[]{0x7C401E001001F070L});
    public static final BitSet FOLLOW_35 = new BitSet(new long[]{0x0000008000000000L});
    public static final BitSet FOLLOW_36 = new BitSet(new long[]{0x0000010000000000L});
    public static final BitSet FOLLOW_37 = new BitSet(new long[]{0x0000020000000000L});
    public static final BitSet FOLLOW_38 = new BitSet(new long[]{0x0000040000000000L});
    public static final BitSet FOLLOW_39 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_40 = new BitSet(new long[]{0x0000000040000000L});
    public static final BitSet FOLLOW_41 = new BitSet(new long[]{0x0000200000000000L});
    public static final BitSet FOLLOW_42 = new BitSet(new long[]{0x0000200000000002L});
    public static final BitSet FOLLOW_43 = new BitSet(new long[]{0x0000400000000000L});
    public static final BitSet FOLLOW_44 = new BitSet(new long[]{0x0000400000000002L});
    public static final BitSet FOLLOW_45 = new BitSet(new long[]{0x0001800000000000L});
    public static final BitSet FOLLOW_46 = new BitSet(new long[]{0x0001800000000002L});
    public static final BitSet FOLLOW_47 = new BitSet(new long[]{0x0000800000000000L});
    public static final BitSet FOLLOW_48 = new BitSet(new long[]{0x001E000000000000L});
    public static final BitSet FOLLOW_49 = new BitSet(new long[]{0x001E000000000002L});
    public static final BitSet FOLLOW_50 = new BitSet(new long[]{0x0002000000000000L});
    public static final BitSet FOLLOW_51 = new BitSet(new long[]{0x0004000000000000L});
    public static final BitSet FOLLOW_52 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_53 = new BitSet(new long[]{0x0060000000000000L});
    public static final BitSet FOLLOW_54 = new BitSet(new long[]{0x0060000000000002L});
    public static final BitSet FOLLOW_55 = new BitSet(new long[]{0x0020000000000000L});
    public static final BitSet FOLLOW_56 = new BitSet(new long[]{0x0180000000000000L});
    public static final BitSet FOLLOW_57 = new BitSet(new long[]{0x0180000000000002L});
    public static final BitSet FOLLOW_58 = new BitSet(new long[]{0x0080000000000000L});
    public static final BitSet FOLLOW_59 = new BitSet(new long[]{0x0200000000000000L});
    public static final BitSet FOLLOW_60 = new BitSet(new long[]{0x0400000000000000L});
    public static final BitSet FOLLOW_61 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_62 = new BitSet(new long[]{0x7C40000030003070L});
    public static final BitSet FOLLOW_63 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_64 = new BitSet(new long[]{0x0000000000000040L});
    public static final BitSet FOLLOW_65 = new BitSet(new long[]{0x0000000000003000L});
    public static final BitSet FOLLOW_66 = new BitSet(new long[]{0x0800000000000000L});
    public static final BitSet FOLLOW_67 = new BitSet(new long[]{0x1000000000000000L});
    public static final BitSet FOLLOW_68 = new BitSet(new long[]{0x2000000000000000L});
    public static final BitSet FOLLOW_69 = new BitSet(new long[]{0x4000000000000000L});

}