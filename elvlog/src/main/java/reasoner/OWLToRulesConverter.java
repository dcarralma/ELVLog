package reasoner;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLAnnotation;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLIrreflexiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLObjectHasSelf;
import org.semanticweb.owlapi.model.OWLObjectHasValue;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
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
import org.semanticweb.owlapi.model.SWRLIndividualArgument;
import org.semanticweb.owlapi.model.SWRLRule;
import org.semanticweb.owlapi.model.SWRLVariable;
import org.semanticweb.vlog4j.core.model.api.AbstractConstant;
import org.semanticweb.vlog4j.core.model.api.Conjunction;
import org.semanticweb.vlog4j.core.model.api.PositiveLiteral;
import org.semanticweb.vlog4j.core.model.api.Rule;
import org.semanticweb.vlog4j.core.model.api.Term;
import org.semanticweb.vlog4j.core.model.api.UniversalVariable;
import org.semanticweb.vlog4j.core.model.api.Variable;
import org.semanticweb.vlog4j.core.model.implementation.Expressions;

import uk.ac.manchester.cs.owl.owlapi.OWLObjectHasSelfImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectSomeValuesFromImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLSubClassOfAxiomImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLSubPropertyChainAxiomImpl;

public class OWLToRulesConverter {

	private Set<Rule> rules = new HashSet<Rule>();
	private Set<Rule> subRoleSelfRules = new HashSet<Rule>();
	private boolean containsSelf = false;

	private static Variable vX = Expressions.makeUniversalVariable("VX");
	private static Variable vY = Expressions.makeUniversalVariable("VY");
	private int freshVarCounter = 0;
	private int freshConstCounter = 0;
	private static String variablePref = "V";
	private static String constantPref = "cons";
	OWLDataFactory factory = OWLManager.getOWLDataFactory();

	public OWLToRulesConverter() {

	}

	public Set<Rule> transform(OWLOntology ontology) {
		// Transforming axioms to rules
		ontology.axioms().forEach(axiom -> transformAxiomToRule(axiom));

		// Adding self rules
		if (containsSelf) {
			ontology.objectPropertiesInSignature().forEach(role -> {
				PositiveLiteral roleXX = Expressions.makePositiveLiteral(role.toString(), vX, vX);
				PositiveLiteral namedX = Expressions.makePositiveLiteral(SpecialURIs.owlNamedIndividual, vX);
				PositiveLiteral selfRoleX = Expressions.makePositiveLiteral(roleToRoleSelfConcept(role), vX);

				rules.add(Expressions.makeRule(Expressions.makePositiveConjunction(selfRoleX),
						Expressions.makeConjunction(roleXX, namedX)));
				rules.add(Expressions.makeRule(Expressions.makePositiveConjunction(roleXX),
						Expressions.makeConjunction(selfRoleX, namedX)));
			});
			rules.addAll(subRoleSelfRules);
		}

		return rules;
	}

	private void transformAxiomToRule(OWLAxiom axiom) {

		switch (axiom.getAxiomType().toString()) {
		case "EquivalentClasses":
			// C1 equiv ... equiv Cn
			for (OWLSubClassOfAxiom equivSubClassOfAxiom : ((OWLEquivalentClassesAxiom) axiom).asOWLSubClassOfAxioms())
				processSubClassOfAxiom(equivSubClassOfAxiom);
			break;

		case "SubClassOf":
			// C sqsubseteq D
			processSubClassOfAxiom((OWLSubClassOfAxiom) axiom);
			break;

		case "DisjointClasses":
			// C1 sqcap ... sqcap Cn sqsubseteq bot
			for (OWLSubClassOfAxiom disjSubClassOfAxiom : ((OWLDisjointClassesAxiom) axiom).asOWLSubClassOfAxioms())
				processSubClassOfAxiom(disjSubClassOfAxiom);
			break;

		case "ObjectPropertyDomain":
			// dom(R) sqsubseteq D
			OWLObjectPropertyDomainAxiom domainAxiom = (OWLObjectPropertyDomainAxiom) axiom;
			OWLObjectSomeValuesFrom subClass = new OWLObjectSomeValuesFromImpl(domainAxiom.getProperty(),
					factory.getOWLThing());
			processSubClassOfAxiom(
					new OWLSubClassOfAxiomImpl(subClass, domainAxiom.getDomain(), new HashSet<OWLAnnotation>()));
			break;

		case "ObjectPropertyRange":
			// ran(R) sqsubseteq D
			OWLObjectPropertyRangeAxiom rangeAxiom = (OWLObjectPropertyRangeAxiom) axiom;
			Conjunction<PositiveLiteral> head = conceptExpToPosConjunction(rangeAxiom.getRange(), vY, true);
			Conjunction<PositiveLiteral> body = Expressions.makePositiveConjunction(
					Expressions.makePositiveLiteral(rangeAxiom.getProperty().toString(), vX, vY));
			rules.add(Expressions.makePositiveLiteralsRule(head, body));
			break;

		case "ReflexiveObjectProperty":
			// Ref(R)
			OWLReflexiveObjectPropertyAxiom reflexiveAxiom = ((OWLReflexiveObjectPropertyAxiom) axiom);
			OWLObjectHasSelf selfSuperClass = new OWLObjectHasSelfImpl(reflexiveAxiom.getProperty());
			processSubClassOfAxiom(
					new OWLSubClassOfAxiomImpl(factory.getOWLThing(), selfSuperClass, new HashSet<OWLAnnotation>()));
			containsSelf = true;
			break;

		case "IrrefexiveObjectProperty":
			// Irref(R)
			OWLIrreflexiveObjectPropertyAxiom irreflexiveAxiom = ((OWLIrreflexiveObjectPropertyAxiom) axiom);
			OWLObjectHasSelf selfSubClass = new OWLObjectHasSelfImpl(irreflexiveAxiom.getProperty());
			processSubClassOfAxiom(
					new OWLSubClassOfAxiomImpl(selfSubClass, factory.getOWLNothing(), new HashSet<OWLAnnotation>()));
			containsSelf = true;
			break;

		case "EquivalentObjectProperties":
			// R equiv S
			OWLEquivalentObjectPropertiesAxiom equivPropertiesAxiom = (OWLEquivalentObjectPropertiesAxiom) axiom;
			for (OWLSubObjectPropertyOfAxiom equivSubObjectPropertyAxiom : equivPropertiesAxiom
					.asSubObjectPropertyOfAxioms()) {
				processSubObjectPropertyAxiom(equivSubObjectPropertyAxiom);
			}
			break;

		case "SubObjectPropertyOf":
			// R sqsubseteq S
			processSubObjectPropertyAxiom((OWLSubObjectPropertyOfAxiom) axiom);
			break;

		case "SubPropertyChainOf":
			// R1 o ... o Rn sqsubseteq S with n > 1
			processChainOfAxiom((OWLSubPropertyChainOfAxiom) axiom);
			break;

		case "TransitiveObjectProperty":
			// Tran(R)
			OWLTransitiveObjectPropertyAxiom transitivityAxiom = (OWLTransitiveObjectPropertyAxiom) axiom;
			OWLObjectPropertyExpression transitiveProperty = transitivityAxiom.getProperty();
			List<OWLObjectPropertyExpression> chain = new ArrayList<OWLObjectPropertyExpression>();
			chain.add(transitiveProperty);
			chain.add(transitiveProperty);
			processChainOfAxiom(
					new OWLSubPropertyChainAxiomImpl(chain, transitiveProperty, new HashSet<OWLAnnotation>()));
			break;

		case "Rule":
			// SWRL Rule
			processSWRLRule((SWRLRule) axiom);
			break;

		case "ClassAssertion":
			// C(a)
			System.out.println("WARNING!!! Class assertion in the TBox: " + axiom);
			break;

		case "ObjectPropertyAssertion":
			// R(a, b)
			System.out.println("WARNING!!! Role assertion in the TBox: " + axiom);
			break;

		case "NegativeObjectPropertyAssertion":
			// lnot R(a, b)
			System.out.println("WARNING!!! Negative role assertion in the TBox: " + axiom);
			break;

		case "SameIndividual":
			// a1 approx ... approx an
			System.out.println("WARNING!!! Same individuals assertion in the TBox: " + axiom);
			break;

		case "DifferentIndividuals":
			// a not approx b
			System.out.println("WARNING!!! Different individuals assertion in the TBox: " + axiom);
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
	}

	private void processSubClassOfAxiom(OWLSubClassOfAxiom subClassOfAxiom) {
		freshVarCounter = 0;
		rules.add(Expressions.makePositiveLiteralsRule(
				conceptExpToPosConjunction(subClassOfAxiom.getSuperClass(), vX, true),
				conceptExpToPosConjunction(subClassOfAxiom.getSubClass(), vX, false)));
	}

	private void processSubObjectPropertyAxiom(OWLSubObjectPropertyOfAxiom subObjectPropertyOfAxiom) {
		OWLObjectProperty subRole = (OWLObjectProperty) subObjectPropertyOfAxiom.getSubProperty();
		OWLObjectProperty superRole = (OWLObjectProperty) subObjectPropertyOfAxiom.getSuperProperty();

		rules.add(Expressions.makeRule(Expressions.makePositiveLiteral(superRole.toString(), vX, vY),
				Expressions.makePositiveLiteral(subRole.toString(), vX, vY)));
		rules.add(Expressions.makeRule(Expressions.makePositiveLiteral(roleToRoleSelfConcept(superRole), vX),
				Expressions.makePositiveLiteral(roleToRoleSelfConcept(subRole), vX)));
	}

	private void processChainOfAxiom(OWLSubPropertyChainOfAxiom chainOfAxiom) {
		freshVarCounter = 0;
		List<OWLObjectPropertyExpression> roleChain = chainOfAxiom.getPropertyChain();
		ArrayList<PositiveLiteral> bodyAtoms = new ArrayList<PositiveLiteral>();
		for (OWLObjectPropertyExpression chainedRole : roleChain)
			bodyAtoms.add(Expressions.makePositiveLiteral(chainedRole.toString(),
					Expressions.makeUniversalVariable(variablePref + Integer.toString(freshVarCounter)),
					Expressions.makeUniversalVariable(variablePref + Integer.toString(++freshVarCounter))));
		Conjunction<PositiveLiteral> body = Expressions.makePositiveConjunction(bodyAtoms);
		Conjunction<PositiveLiteral> head = Expressions.makePositiveConjunction(Expressions.makePositiveLiteral(
				chainOfAxiom.getSuperProperty().toString(), Expressions.makeUniversalVariable(variablePref + "0"),
				Expressions.makeUniversalVariable(variablePref + freshVarCounter)));
		rules.add(Expressions.makePositiveLiteralsRule(head, body));
	}

	private void processSWRLRule(SWRLRule safeRule) {
		freshVarCounter = 0;
		Set<SWRLAtom> swrlBodyAtoms = safeRule.body().collect(Collectors.toSet());
		Set<SWRLAtom> swrlHeadAtoms = safeRule.head().collect(Collectors.toSet());
		Set<SWRLAtom> swrlAtoms = new HashSet<SWRLAtom>();
		swrlAtoms.addAll(swrlBodyAtoms);
		swrlAtoms.addAll(swrlHeadAtoms);

		HashMap<SWRLArgument, UniversalVariable> safeVarToUnivVarMap = new HashMap<SWRLArgument, UniversalVariable>();
		for (SWRLAtom safeAtom : swrlAtoms)
			for (SWRLArgument safeArgument : safeAtom.allArguments().collect(Collectors.toSet()))
				if (safeArgument instanceof SWRLVariable)
					safeVarToUnivVarMap.putIfAbsent(safeArgument,
							Expressions.makeUniversalVariable(variablePref + Integer.toString(++freshVarCounter)));

		ArrayList<PositiveLiteral> headAtoms = new ArrayList<PositiveLiteral>();
		for (SWRLAtom safeHeadAtom : swrlHeadAtoms)
			headAtoms.add(swrlAtomToPositiveLiteral(safeHeadAtom, safeVarToUnivVarMap));
		Conjunction<PositiveLiteral> head = Expressions.makePositiveConjunction(headAtoms);

		ArrayList<PositiveLiteral> bodyAtoms = new ArrayList<PositiveLiteral>();
		for (SWRLAtom safeBodyAtom : swrlBodyAtoms)
			bodyAtoms.add(swrlAtomToPositiveLiteral(safeBodyAtom, safeVarToUnivVarMap));
		for (UniversalVariable variable : safeVarToUnivVarMap.values())
			bodyAtoms.add(Expressions.makePositiveLiteral(SpecialURIs.owlNamedIndividual, variable));
		Conjunction<PositiveLiteral> body = Expressions.makePositiveConjunction(bodyAtoms);

		rules.add(Expressions.makePositiveLiteralsRule(head, body));
	}

	public PositiveLiteral swrlAtomToPositiveLiteral(SWRLAtom safeBodyAtom,
			HashMap<SWRLArgument, UniversalVariable> safeVarToXVarMap) {
		List<Term> terms = new ArrayList<Term>();
		for (SWRLArgument arg : safeBodyAtom.allArguments().collect(Collectors.toList()))
			if (arg instanceof SWRLVariable)
				terms.add(safeVarToXVarMap.get(arg));
			else if (arg instanceof SWRLIndividualArgument)
				terms.add(Expressions.makeAbstractConstant(((SWRLIndividualArgument) arg).getIndividual().toString()));
		
		return Expressions.makePositiveLiteral(safeBodyAtom.getPredicate().toString(), terms);
	}

	private Conjunction<PositiveLiteral> conceptExpToPosConjunction(OWLClassExpression conceptExp, Term term,
			boolean buildingHead) {
		return Expressions.makeConjunction(conceptExpToAtoms(conceptExp, term, buildingHead));
	}

	private List<PositiveLiteral> conceptExpToAtoms(OWLClassExpression conceptExp, Term term, boolean buildingHead) {

		ArrayList<PositiveLiteral> literals = new ArrayList<PositiveLiteral>();

		switch (conceptExp.getClassExpressionType().toString()) {

		case "ObjectIntersectionOf":
			// C1 scap ... sqcap Cn
			OWLObjectIntersectionOf intConceptExp = (OWLObjectIntersectionOf) conceptExp;
			for (OWLClassExpression conjunctConceptExp : intConceptExp.asConjunctSet())
				literals.addAll(conceptExpToAtoms(conjunctConceptExp, term, buildingHead));
			break;

		case "ObjectMinCardinality":
			OWLObjectMinCardinality minCardConceptExp = (OWLObjectMinCardinality) conceptExp;
			if (minCardConceptExp.getCardinality() != 1) {
				System.out.println(
						"WARNING!!! Illegal ObjectMinCardinality concept expression at StoreInitializer.java." + "\n"
								+ " > " + conceptExp.getClassExpressionType().toString() + "\n" + " > " + conceptExp);
				break;
			} else {
				conceptExp = new OWLObjectSomeValuesFromImpl(minCardConceptExp.getProperty(),
						minCardConceptExp.getFiller());
			}

		case "ObjectSomeValuesFrom":
			// exists R.C
			OWLObjectSomeValuesFrom existConceptExp = (OWLObjectSomeValuesFrom) conceptExp;
			OWLClassExpression filler = existConceptExp.getFiller();
			Term freshTerm;
			if (buildingHead) {
				freshTerm = Expressions.makeAbstractConstant(constantPref + ++freshConstCounter);
				if (!filler.isOWLThing())
					literals.add(Expressions.makePositiveLiteral(SpecialURIs.owlThing, freshTerm));
			} else
				freshTerm = Expressions.makeUniversalVariable(variablePref + ++freshVarCounter);
			literals.add(Expressions.makePositiveLiteral(existConceptExp.getProperty().toString(), term, freshTerm));
			literals.addAll(conceptExpToAtoms(filler, freshTerm, buildingHead));
			break;

		case "ObjectOneOf":
			// {a1} sqcup ... sqcup {an}
			OWLObjectOneOf nominalConceptExpression = (OWLObjectOneOf) conceptExp;
			if (nominalConceptExpression.individuals().collect(Collectors.toSet()).size() > 1) {
				System.out.println("WARNING!!! Illegal OWLObjectOneOf expression at StoreInitializer.java." + "\n"
						+ " > " + nominalConceptExpression + "\n");
			}
			AbstractConstant nominalConstant = Expressions.makeAbstractConstant(
					nominalConceptExpression.individuals().collect(Collectors.toSet()).iterator().next().toString());
			literals.add(Expressions.makePositiveLiteral(SpecialURIs.owlSameAs, term, nominalConstant));
			break;

		case "ObjectHasSelf":
			// exists R.Self
			containsSelf = true;
			OWLObjectHasSelf selfConceptExp = (OWLObjectHasSelf) conceptExp;
			String roleSelfConcept = roleToRoleSelfConcept((OWLObjectProperty) selfConceptExp.getProperty());
			literals.add(Expressions.makePositiveLiteral(roleSelfConcept, term));
			break;

		case "ObjectHasValue":
			// exists R.{a}
			OWLObjectHasValue hasValueExp = (OWLObjectHasValue) conceptExp;
			AbstractConstant valueConstant = Expressions.makeAbstractConstant(hasValueExp.getFiller().toString());
			literals.add(Expressions.makePositiveLiteral(hasValueExp.getProperty().toString(), term, valueConstant));
			break;

		case "Class":
			// A
			literals.add(Expressions.makePositiveLiteral(conceptExp.toString(), term));
			break;

		default:
			System.out.println("WARNING!!! Unrecognized type of concept expression at StoreInitializer.java." + "\n"
					+ " > " + conceptExp.getClassExpressionType().toString() + "\n" + " > " + conceptExp);
			break;
		}

		return literals;
	}

	private String roleToRoleSelfConcept(OWLObjectProperty role) {
		return role.toString().substring(0, role.toString().length() - 1) + "Self>";
	}

}
