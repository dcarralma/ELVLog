package reasoner;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLIrreflexiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLObjectHasSelf;
import org.semanticweb.owlapi.model.OWLObjectHasValue;
import org.semanticweb.owlapi.model.OWLObjectMinCardinality;
import org.semanticweb.owlapi.model.OWLObjectOneOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLReflexiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubObjectPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubPropertyChainOfAxiom;
import org.semanticweb.owlapi.model.OWLTransitiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.SWRLArgument;
import org.semanticweb.owlapi.model.SWRLAtom;
import org.semanticweb.owlapi.model.SWRLRule;
import org.semanticweb.vlog4j.core.model.api.Conjunction;
import org.semanticweb.vlog4j.core.model.api.Literal;
import org.semanticweb.vlog4j.core.model.api.PositiveLiteral;
import org.semanticweb.vlog4j.core.model.api.Rule;
import org.semanticweb.vlog4j.core.model.implementation.Expressions;

import uk.ac.manchester.cs.owl.owlapi.OWLObjectSomeValuesFromImpl;

public class OWLToRulesConverter {

	private int freshVarCounter;
	private int freshConstCounter;
	private Set<VRule> subRoleSelfRules;
	private boolean containsSelf;

	private static String vX = "VX";
	private static String vY = "VY";
	private static String vZ = "VZ";

	public OWLToRulesConverter() {
		freshVarCounter = 0;
		freshConstCounter = 0;
		subRoleSelfRules = new HashSet<VRule>();
		containsSelf = false;
	}

	public Set<Rule> transform(OWLOntology ontology) {
		Set<VRule> rules = new HashSet<VRule>();
		// Transforming axioms to rules
		for (OWLAxiom axiom : ontology.getAxioms())
			transformAxiomToRule(rules, axiom);

		// Adding self rules
		if (containsSelf) {
			for (OWLObjectProperty role : ontology.getObjectPropertiesInSignature()) {
				rules.add(new VRule(new VAtom(roleToRoleSelfConcept(role), vX), new VAtom(role, vX, vX),
						new VAtom(SpecialURIs.owlNamedIndividual, vX)));
				rules.add(new VRule(new VAtom(role, vX, vX), new VAtom(SpecialURIs.owlNamedIndividual, vX),
						new VAtom(roleToRoleSelfConcept(role), vX)));
			}

			rules.addAll(subRoleSelfRules);
		}

		Set<Rule> vlogRules = new HashSet<Rule>();
		for (VRule rule : rules) {
			List<PositiveLiteral> headAtoms = new ArrayList<PositiveLiteral>();
			for (VAtom headAtom : rule.getHead())
				headAtoms.add(headAtom.toVLogAtom());
			Conjunction<PositiveLiteral> head = Expressions.makePositiveConjunction(headAtoms);

			List<Literal> bodyAtoms = new ArrayList<Literal>();
			for (VAtom bodyAtom : rule.getBody())
				bodyAtoms.add(bodyAtom.toVLogAtom());
			Conjunction<Literal> body = Expressions.makeConjunction(bodyAtoms);

			vlogRules.add(Expressions.makeRule(head, body));
		}

		return vlogRules;
	}

	private Object transformAxiomToRule(Set<VRule> rules, OWLAxiom axiom) {
		freshVarCounter = 0;
		switch (axiom.getAxiomType().toString()) {

		case "EquivalentClasses":
			// C1 equiv ... equiv Cn
			List<OWLClassExpression> equivConcepts = ((OWLEquivalentClassesAxiom) axiom).getClassExpressionsAsList();
			for (int i = 0; i < equivConcepts.size(); i++)
				for (int j = 0; j < equivConcepts.size(); j++)
					if (i != j)
						rules.add(new VRule(expToAtoms(equivConcepts.get(i), vX, true),
								expToAtoms(equivConcepts.get(j), vX, false)));
			break;

		case "SubClassOf":
			// C sqsubseteq D
			OWLSubClassOfAxiom subClassOfAxiom = (OWLSubClassOfAxiom) axiom;
			rules.add(new VRule(expToAtoms(subClassOfAxiom.getSuperClass(), vX, true),
					expToAtoms(subClassOfAxiom.getSubClass(), vX, false)));
			break;

		case "DisjointClasses":
			// C1 sqcap ... sqcap Cn sqsubseteq bot
			List<OWLClassExpression> disjConcepts = ((OWLDisjointClassesAxiom) axiom).getClassExpressionsAsList();
			for (int i = 0; i < disjConcepts.size(); i++)
				for (int j = i + 1; j < disjConcepts.size(); j++) {
					ArrayList<VAtom> bodyAtoms = new ArrayList<VAtom>();
					bodyAtoms.addAll(expToAtoms(disjConcepts.get(i), vX, false));
					bodyAtoms.addAll(expToAtoms(disjConcepts.get(j), vX, false));
					rules.add(new VRule(new VAtom(SpecialURIs.owlNothing, vX), bodyAtoms));
				}
			break;

		case "ObjectPropertyDomain":
			// dom(R) sqsubseteq D
			OWLObjectPropertyDomainAxiom domainAxiom = (OWLObjectPropertyDomainAxiom) axiom;
			rules.add(new VRule(expToAtoms(domainAxiom.getDomain(), vX, true),
					new VAtom((OWLObjectProperty) domainAxiom.getProperty(), vX, vY)));
			break;

		case "ObjectPropertyRange":
			// ran(R) sqsubseteq D
			OWLObjectPropertyRangeAxiom rangeAxiom = (OWLObjectPropertyRangeAxiom) axiom;
			rules.add(new VRule(expToAtoms(rangeAxiom.getRange(), vY, true),
					new VAtom((OWLObjectProperty) rangeAxiom.getProperty(), vX, vY)));
			break;

		case "ReflexiveObjectProperty":
			// Ref(R)
			OWLObjectProperty reflexiveRole = (OWLObjectProperty) ((OWLReflexiveObjectPropertyAxiom) axiom)
					.getProperty();
			String roleSelfConcept = roleToRoleSelfConcept(reflexiveRole);
			rules.add(new VRule(new VAtom(roleSelfConcept, vX), new VAtom(SpecialURIs.owlThing, vX)));
			containsSelf = true;
			break;

		case "IrrefexiveObjectProperty":
			// Irref(R)
			OWLObjectProperty irreflexiveRole = (OWLObjectProperty) ((OWLIrreflexiveObjectPropertyAxiom) axiom)
					.getProperty();
			rules.add(new VRule(new VAtom(SpecialURIs.owlNothing, vX),
					new VAtom(roleToRoleSelfConcept(irreflexiveRole), vX)));
			containsSelf = true;
			break;

		case "EquivalentObjectProperties":
			// R equiv S
			ArrayList<OWLObjectPropertyExpression> equivRoles = new ArrayList<OWLObjectPropertyExpression>(
					((OWLEquivalentObjectPropertiesAxiom) axiom).getObjectPropertiesInSignature());
			// List<OWLObjectPropertyExpression> equivRoles = new
			// ArrayList<OWLObjectPropertyExpression>(
			// ((OWLEquivalentObjectPropertiesAxiom) axiom).properties());
			for (int i = 0; i < equivRoles.size(); i++)
				for (int j = 0; j < equivRoles.size(); j++)
					if (i != j) {
						OWLObjectProperty objectRolei = (OWLObjectProperty) equivRoles.get(i);
						OWLObjectProperty objectRolej = (OWLObjectProperty) equivRoles.get(j);
						rules.add(new VRule(new VAtom(objectRolei, vX, vY), new VAtom(objectRolej, vX, vY)));
						subRoleSelfRules.add(new VRule(new VAtom(roleToRoleSelfConcept(objectRolei), vX),
								new VAtom(roleToRoleSelfConcept(objectRolej), vX)));
					}
			break;

		case "SubObjectPropertyOf":
			// R sqsubseteq S
			OWLSubObjectPropertyOfAxiom subObjectPropertyOfAxiom = (OWLSubObjectPropertyOfAxiom) axiom;
			OWLObjectProperty superRole = (OWLObjectProperty) subObjectPropertyOfAxiom.getSuperProperty();
			OWLObjectProperty subRole = (OWLObjectProperty) subObjectPropertyOfAxiom.getSubProperty();
			rules.add(new VRule(new VAtom(superRole, vX, vY), new VAtom(subRole, vX, vY)));
			subRoleSelfRules.add(new VRule(new VAtom(roleToRoleSelfConcept(superRole), vX),
					new VAtom(roleToRoleSelfConcept(subRole), vX)));
			break;

		case "SubPropertyChainOf":
			// R1 o ... o Rn sqsubseteq S with n > 1
			OWLSubPropertyChainOfAxiom chainOfAxiom = (OWLSubPropertyChainOfAxiom) axiom;
			List<OWLObjectPropertyExpression> roleChain = chainOfAxiom.getPropertyChain();
			ArrayList<VAtom> bodyAtoms = new ArrayList<VAtom>();
			for (OWLObjectPropertyExpression chainedRole : roleChain)
				bodyAtoms.add(new VAtom((OWLObjectProperty) chainedRole, vX + freshVarCounter, vX + ++freshVarCounter));
			rules.add(new VRule(
					new VAtom((OWLObjectProperty) chainOfAxiom.getSuperProperty(), vX + "0", vX + freshVarCounter),
					bodyAtoms));
			// System.out.println(new VRule(new VAtom((OWLObjectProperty)
			// chainOfAxiom.getSuperProperty(), vX + "0", vX + freshVarCounter),
			// bodyAtoms).toOxRules());
			break;

		case "TransitiveObjectProperty":
			// Tran(R)
			String transitiveRoleR = ((OWLTransitiveObjectPropertyAxiom) axiom).getProperty().toString();
			rules.add(new VRule(new VAtom(transitiveRoleR, vX, vY), new VAtom(transitiveRoleR, vX, vZ),
					new VAtom(transitiveRoleR, vZ, vY)));
			break;

		case "Rule":
			// SWRL Rule
			// System.out.println(axiom);
			rules.add(swrlRuleToRule((SWRLRule) axiom));
			break;

		case "ClassAssertion":
			// C(a)
			System.out.println("WARNING!!! Class assertion in the TBox: " + axiom);
			// OWLClassAssertionAxiom classAssertion = (OWLClassAssertionAxiom) axiom;
			// OWLClassExpression classExpressionC = classAssertion.getClassExpression();
			// OWLIndividual individuala = classAssertion.getIndividual();
			// if (!classExpressionC.isOWLThing()) {
			// if
			// (classExpressionC.getClassExpressionType().equals(ClassExpressionType.OWL_CLASS))
			// store.addTriples(new VAtom((OWLClass) classExpressionC,
			// individuala).toGroundTermFact());
			// else if
			// (classExpressionC.getComplementNNF().getClassExpressionType().equals(ClassExpressionType.OWL_CLASS))
			// {
			// store.importText(
			// new VRule(new VAtom(SWURIs.owlNothing, individuala), new VAtom((OWLClass)
			// classExpressionC.getComplementNNF(), individuala)).toOxRules());
			// } else {
			// System.out.println("WARNING!!! Invalid ClassAssertion axiom at ELVNReasoner
			// at ELVNReasoner.java." + "\n" + " > " + classAssertion + "\n" + " > "
			// + classExpressionC + "\n");
			// validOntology = false;
			// }
			// }
			break;

		case "ObjectPropertyAssertion":
			// R(a, b)
			System.out.println("WARNING!!! Role assertion in the TBox: " + axiom);
			// OWLObjectPropertyAssertionAxiom objectAssertion =
			// (OWLObjectPropertyAssertionAxiom) axiom;
			// store.addTriples(new VAtom((OWLObjectProperty) objectAssertion.getProperty(),
			// objectAssertion.getSubject(),
			// objectAssertion.getObject()).toGroundTermFact());
			break;

		case "NegativeObjectPropertyAssertion":
			// lnot R(a, b)
			System.out.println("WARNING!!! Negative role assertion in the TBox: " + axiom);
			// OWLNegativeObjectPropertyAssertionAxiom negativeRoleAssertion =
			// (OWLNegativeObjectPropertyAssertionAxiom) axiom;
			// store.importText(new VRule(new VAtom(SWURIs.owlNothing,
			// negativeRoleAssertion.getSubject()),
			// new VAtom((OWLObjectProperty) negativeRoleAssertion.getProperty(),
			// negativeRoleAssertion.getSubject(), negativeRoleAssertion.getObject()))
			// .toOxRules());
			break;

		case "SameIndividual":
			// a1 approx ... approx an
			System.out.println("WARNING!!! Same individuals assertion in the TBox: " + axiom);
			// OWLSameIndividualAxiom sameIndividualAxiom = (OWLSameIndividualAxiom) axiom;
			// List<OWLIndividual> individualList =
			// sameIndividualAxiom.getIndividualsAsList();
			// for (int i = 0; i < individualList.size(); i++)
			// for (int j = i + 1; j < individualList.size(); j++)
			// store.addTriples(new VAtom(SWURIs.owlSameAs, individualList.get(i),
			// individualList.get(j)).toGroundTermFact());
			break;

		case "DifferentIndividuals":
			// a not approx b
			System.out.println("WARNING!!! Different individuals assertion in the TBox: " + axiom);
			// OWLDifferentIndividualsAxiom differentIndividualAxiom =
			// (OWLDifferentIndividualsAxiom) axiom;
			// List<OWLIndividual> differentIndividualsList =
			// differentIndividualAxiom.getIndividualsAsList();
			// for (int i = 0; i < differentIndividualsList.size(); i++)
			// for (int j = i + 1; j < differentIndividualsList.size(); j++)
			// store.importText(new VRule(new VAtom(SWURIs.owlNothing,
			// differentIndividualsList.get(i)),
			// new VAtom(SWURIs.owlSameAs, differentIndividualsList.get(i),
			// differentIndividualsList.get(j))).toOxRules());
			break;

		case "AnnotationAssertion":
			break;

		case "Declaration":
			break;

		default:
			System.out.println("WARNING!!! Unrecognized type of axiom at StoreInitializer.java." + "\n" + " > "
					+ axiom.getAxiomType().toString() + "\n" + " > " + axiom + "\n");
			break;
		}
		return null;
	}

	private VRule swrlRuleToRule(SWRLRule safeRule) {

		Set<SWRLAtom> swrlBody = safeRule.getBody();
		Set<SWRLAtom> swrlHead = safeRule.getHead();

		Set<SWRLAtom> swrlAtoms = new HashSet<SWRLAtom>();
		swrlAtoms.addAll(swrlBody);
		swrlAtoms.addAll(swrlHead);

		HashMap<SWRLArgument, String> safeVarToXVarMap = new HashMap<SWRLArgument, String>();
		for (SWRLAtom safeAtom : swrlAtoms)
			for (SWRLArgument safeArgument : safeAtom.getAllArguments())
				if (safeArgument.toString().contains("Variable"))
					safeVarToXVarMap.putIfAbsent(safeArgument, vX + Integer.toString(++freshVarCounter));

		ArrayList<VAtom> head = new ArrayList<VAtom>();
		for (SWRLAtom safeHeadAtom : swrlHead)
			head.add(new VAtom(safeHeadAtom, safeVarToXVarMap));

		ArrayList<VAtom> body = new ArrayList<VAtom>();
		for (SWRLAtom safeBodyAtom : swrlBody)
			body.add(new VAtom(safeBodyAtom, safeVarToXVarMap));
		for (String variable : safeVarToXVarMap.values())
			body.add(new VAtom(SpecialURIs.owlNamedIndividual, variable));

		// System.out.println(safeRule);
		// System.out.println(new VRule(head, body).toOxRules());

		return new VRule(head, body);
	}

	private ArrayList<VAtom> expToAtoms(OWLClassExpression conceptExpression, String term, boolean buildingHead) {

		ArrayList<VAtom> atoms = new ArrayList<VAtom>();

		switch (conceptExpression.getClassExpressionType().toString()) {

		case "ObjectIntersectionOf":
			// C1 scap ... sqcap Cn
			for (OWLClassExpression conjunctClassCi : conceptExpression.asConjunctSet())
				atoms.addAll(expToAtoms(conjunctClassCi, term, buildingHead));
			break;

		case "ObjectMinCardinality":
			OWLObjectMinCardinality minCardRC = (OWLObjectMinCardinality) conceptExpression;
			if (minCardRC.getCardinality() != 1) {
				System.out
						.println("WARNING!!! Illegal ObjectMinCardinality concept expression at StoreInitializer.java."
								+ "\n" + " > " + conceptExpression.getClassExpressionType().toString() + "\n" + " > "
								+ conceptExpression);
			} else
				conceptExpression = new OWLObjectSomeValuesFromImpl(minCardRC.getProperty(), minCardRC.getFiller());
		case "ObjectSomeValuesFrom":
			// exists R.C
			OWLObjectSomeValuesFrom existConceptRC = (OWLObjectSomeValuesFrom) conceptExpression;
			OWLClassExpression fillerC = existConceptRC.getFiller();
			String freshTerm;
			if (buildingHead) {
				freshTerm = "cons" + ++freshConstCounter;
				if (!fillerC.isOWLThing() && !fillerC.toString().equals("<owl:Thing>"))
					atoms.add(new VAtom(SpecialURIs.owlThing, freshTerm));
			} else
				freshTerm = vX + ++freshVarCounter;
			atoms.add(new VAtom(existConceptRC.getProperty().toString(), term, freshTerm));
			atoms.addAll(expToAtoms(fillerC, freshTerm, buildingHead));
			break;

		case "ObjectOneOf":
			// {a1} sqcup ... sqcup {an}
			OWLObjectOneOf nominalConceptExpression = (OWLObjectOneOf) conceptExpression;
			if (nominalConceptExpression.individuals().collect(Collectors.toSet()).size() > 1) {
				System.out.println("WARNING!!! Illegal OWLObjectOneOf expression at StoreInitializer.java." + "\n"
						+ " > " + nominalConceptExpression + "\n");
			}
			atoms.add(new VAtom(SpecialURIs.owlSameAs,
					nominalConceptExpression.individuals().collect(Collectors.toSet()).iterator().next().toString(),
					term));
			break;

		case "ObjectHasSelf":
			// exists R.Self
			containsSelf = true;
			String roleSelfConcept = roleToRoleSelfConcept(
					(OWLObjectProperty) ((OWLObjectHasSelf) conceptExpression).getProperty());
			atoms.add(new VAtom(roleSelfConcept, term));
			break;

		case "ObjectHasValue":
			// exists R.{a}
			OWLObjectHasValue hasValueExpression = (OWLObjectHasValue) conceptExpression;
			atoms.add(new VAtom((OWLObjectProperty) hasValueExpression.getProperty(), term,
					hasValueExpression.getFiller()));
			break;

		case "Class":
			// A
			atoms.add(new VAtom((OWLClass) conceptExpression, term));
			break;

		default:
			System.out.println("WARNING!!! Unrecognized type of concept expression at StoreInitializer.java." + "\n"
					+ " > " + conceptExpression.getClassExpressionType().toString() + "\n" + " > " + conceptExpression);
			break;
		}

		return atoms;
	}

	private String roleToRoleSelfConcept(OWLObjectProperty role) {
		return role.toString().substring(0, role.toString().length() - 1) + "Self>";
	}

}
