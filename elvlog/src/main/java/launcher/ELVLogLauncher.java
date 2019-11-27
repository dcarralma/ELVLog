package launcher;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.vlog4j.core.model.api.DataSource;
import org.semanticweb.vlog4j.core.model.api.Literal;
import org.semanticweb.vlog4j.core.model.api.Predicate;
import org.semanticweb.vlog4j.core.model.api.Rule;
import org.semanticweb.vlog4j.core.model.api.Term;
import org.semanticweb.vlog4j.core.model.api.Variable;
import org.semanticweb.vlog4j.core.model.implementation.DataSourceDeclarationImpl;
import org.semanticweb.vlog4j.core.model.implementation.Expressions;
import org.semanticweb.vlog4j.core.reasoner.KnowledgeBase;
import org.semanticweb.vlog4j.core.reasoner.QueryResultIterator;
import org.semanticweb.vlog4j.core.reasoner.Reasoner;
import org.semanticweb.vlog4j.core.reasoner.implementation.RdfFileDataSource;
import org.semanticweb.vlog4j.core.reasoner.implementation.VLogReasoner;

import reasoner.OWLToRulesConverter;
import reasoner.SpecialURIs;

public class ELVLogLauncher {

	static Predicate triple = Expressions.makePredicate("triple", 3);

	static Variable vX = Expressions.makeUniversalVariable("VX");
	static Variable vY = Expressions.makeUniversalVariable("VY");
	static Variable vZ = Expressions.makeUniversalVariable("VZ");

	public static void main(String[] arguments) throws OWLOntologyCreationException, IOException {
		String owlOntologyFilePath = "/Users/carralma/Desktop/elvlog-eval-files/ontologies/uniprot/elvlog/uniprot-swrl-el-nf-xml-tbox.owl";
		String dataFilePath = "/Users/carralma/Desktop/elvlog-eval-files/ontologies/uniprot/elvlog/uniprot015.nt";

		long start = System.nanoTime();
		System.out.println(" > TBox axioms into Rules: " + nanosecondsToSeconds(System.nanoTime() - start));
		File owlOntologyFile = new File(owlOntologyFilePath);
		OWLOntology ontology = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(owlOntologyFile);
		OWLToRulesConverter owlToRulesTransformer = new OWLToRulesConverter();
		Set<Rule> ruleSet = owlToRulesTransformer.transform(ontology);
		final KnowledgeBase kb = new KnowledgeBase();
		kb.addStatements(ruleSet);

		System.out.println(" > Instantiating loading rules: " + nanosecondsToSeconds(System.nanoTime() - start));
		Set<Predicate> predicates = new HashSet<Predicate>();
		for (Rule rule : kb.getRules()) {
			Set<Literal> ruleAtoms = new HashSet<Literal>();
			ruleAtoms.addAll(rule.getBody().getLiterals());
			ruleAtoms.addAll(rule.getHead().getLiterals());
			for (Literal atom : ruleAtoms)
				predicates.add(atom.getPredicate());
		}
		predicates.add(Expressions.makePredicate(SpecialURIs.owlNamedIndividual, 1));

		for (Predicate predicate : predicates) {
			Rule rule = null;
			if (predicate.getArity() == 1)
				rule = Expressions.makeRule(Expressions.makePositiveLiteral(predicate, vX),
						Expressions.makePositiveLiteral(triple, vX, vY,
								Expressions.makeAbstractConstant(trim(predicate.getName()))));
			else if (predicate.getArity() == 2)
				rule = Expressions.makeRule(Expressions.makePositiveLiteral(predicate, vX, vY),
						Expressions.makePositiveLiteral(triple, vX,
								Expressions.makeAbstractConstant(trim(predicate.getName())), vY));
			kb.addStatement(rule);
		}

		System.out.println(" > Loading data sources: " + nanosecondsToSeconds(System.nanoTime() - start));
		File dataFile = new File(dataFilePath);
		DataSource dataSource = new RdfFileDataSource(dataFile);
		DataSourceDeclarationImpl ds = new DataSourceDeclarationImpl(triple, dataSource);
		kb.addStatement(ds);

		System.out.println(" > Reasoning: " + nanosecondsToSeconds(System.nanoTime() - start));
		Reasoner reasoner = new VLogReasoner(kb);
		reasoner.reason();

		System.out.println(" > Finished: " + nanosecondsToSeconds(System.nanoTime() - start));

		predicates.add(triple);
		System.out.println(predicates.size());
		visiualiseFactCounts(predicates, reasoner);

		// visualiseFacts(triple, reasoner);

	}

	private static String trim(String name) {
		return name.substring(1, name.length() - 1);
	}

	private static void visiualiseFactCounts(Set<Predicate> predicates, Reasoner reasoner) {
		for (Predicate predicate : predicates) {
			System.out.println(predicate);
			List<Term> variables = new ArrayList<Term>();
			for (int i = 0; i < predicate.getArity(); i++)
				variables.add(Expressions.makeUniversalVariable("VX" + Integer.toString(i)));
			QueryResultIterator iterator = reasoner.answerQuery(Expressions.makePositiveLiteral(predicate, variables),
					true);
			int predicateCount = 0;
			while (iterator.hasNext()) {
				++predicateCount;
				iterator.next();
			}
			System.out.println(" - " + predicate.getName() + " (" + predicate.getArity() + "): " + predicateCount);
		}
	}

	private static String nanosecondsToSeconds(long nanoseconds) {
		return Float.toString(nanoseconds / 1000000000);
	}

	// private static void visualiseFacts(Predicate predicate, Reasoner reasoner) {
	// List<Term> variables = new ArrayList<Term>();
	// for (int i = 0; i < predicate.getArity(); i++)
	// variables.add(Expressions.makeUniversalVariable("VX" + Integer.toString(i)));
	// QueryResultIterator iterator =
	// reasoner.answerQuery(Expressions.makePositiveLiteral(predicate, variables),
	// true);
	// while (iterator.hasNext())
	// System.out.println(iterator.next());
	// System.out.println();
	// }
}

// OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
// OWLDataFactory factory = manager.getOWLDataFactory();
//
// OWLOntology inputOntology = manager
// .loadOntologyFromOntologyDocument(new
// File("/Users/carralma/Desktop/velox-evalution/files/tbox-files/2-normalised-tboxes/uniprot-normalised-tbox.owl"));
// OWLOntology elNormalisedOntology = manager.createOntology();
//
// for (OWLAxiom axiom : inputOntology.getAxioms())
// if (axiom.isOfType(AxiomType.SUBCLASS_OF)) {
// OWLSubClassOfAxiom subClassOfAxiom = (OWLSubClassOfAxiom) axiom;
// OWLClassExpression subClass = subClassOfAxiom.getSubClass();
// OWLClassExpression superClass = subClassOfAxiom.getSuperClass();
//
// if (subClass.getClassExpressionType().equals(ClassExpressionType.OWL_CLASS)
// &&
// superClass.getClassExpressionType().equals(ClassExpressionType.OBJECT_ALL_VALUES_FROM))
// {
// OWLObjectAllValuesFrom allValuesSuperClass = (OWLObjectAllValuesFrom)
// superClass;
// manager.addAxiom(elNormalisedOntology, factory.getOWLSubClassOfAxiom(
// factory.getOWLObjectSomeValuesFrom(allValuesSuperClass.getProperty().getInverseProperty(),
// subClass), allValuesSuperClass.getFiller()));
// System.out.println(axiom);
// System.out.println(factory.getOWLSubClassOfAxiom(factory.getOWLObjectSomeValuesFrom(allValuesSuperClass.getProperty().getInverseProperty(),
// subClass),
// allValuesSuperClass.getFiller()));
// System.out.println();
// } else
// manager.addAxiom(elNormalisedOntology, axiom);
// } else
// manager.addAxiom(elNormalisedOntology, axiom);
//
// manager.saveOntology(elNormalisedOntology, new
// OWLFunctionalSyntaxOntologyFormat(),
// IRI.create(new
