package launcher;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.vlog4j.core.model.api.DataSource;
import org.semanticweb.vlog4j.core.model.api.Predicate;
import org.semanticweb.vlog4j.core.model.api.Rule;
import org.semanticweb.vlog4j.core.model.api.Term;
import org.semanticweb.vlog4j.core.model.implementation.DataSourceDeclarationImpl;
import org.semanticweb.vlog4j.core.model.implementation.Expressions;
import org.semanticweb.vlog4j.core.reasoner.KnowledgeBase;
import org.semanticweb.vlog4j.core.reasoner.QueryResultIterator;
import org.semanticweb.vlog4j.core.reasoner.Reasoner;
import org.semanticweb.vlog4j.core.reasoner.implementation.RdfFileDataSource;
import org.semanticweb.vlog4j.core.reasoner.implementation.VLogReasoner;

import reasoner.OWLToRulesConverter;
import reasoner.SpecialPreds;

public class ELVLogLauncher {

	private static Reasoner reasoner;

	public static void main(String[] arguments) throws OWLOntologyCreationException, IOException {
		String owlOntologyFilePath = arguments[0];
		String dataFilePath = arguments[1];

		// Loading TBox
		long start = System.nanoTime();
		System.out.println(" > Loading TBox: " + nanotoSeconds(System.nanoTime() - start));
		File owlOntologyFile = new File(owlOntologyFilePath);
		OWLOntology ontology = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(owlOntologyFile);

		// Transforming TBox Axioms into Rules
		System.out.println(" > Transforming TBox Axioms into Rules: " + nanotoSeconds(System.nanoTime() - start));
		OWLToRulesConverter owlToRulesTransformer = new OWLToRulesConverter(ontology);
		Set<Rule> ruleSet = owlToRulesTransformer.getRules();
		final KnowledgeBase kb = new KnowledgeBase();
		kb.addStatements(ruleSet);

		// Loading ABox
		System.out.println(" > Loading ABox: " + nanotoSeconds(System.nanoTime() - start));
		File dataFile = new File(dataFilePath);
		DataSource dataSource = new RdfFileDataSource(dataFile);
		DataSourceDeclarationImpl ds = new DataSourceDeclarationImpl(
				Expressions.makePredicate(SpecialPreds.triplePredName, 3), dataSource);
		kb.addStatement(ds);

		// Materialisation
		System.out.println(" > Materialisation: " + nanotoSeconds(System.nanoTime() - start));
		reasoner = new VLogReasoner(kb);
		reasoner.reason();

		// Finished
		System.out.println(" > Finished: " + nanotoSeconds(System.nanoTime() - start));

		// Checking Results
		visiualiseFactCounts(owlToRulesTransformer.getPredicates(), reasoner);
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

	private static String nanotoSeconds(long nanoseconds) {
		return Float.toString(nanoseconds / 1000000000);
	}
}